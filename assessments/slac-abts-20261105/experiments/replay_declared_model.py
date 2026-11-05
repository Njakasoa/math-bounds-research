"""Conditional replay of notebook-declared concentration ODEs, not literal SBML.
No fitting, no stdev interpretation, no external notebook execution.
"""
from pathlib import Path
import zipfile,xml.etree.ElementTree as ET,io,csv,json,hashlib,sys
from fractions import Fraction as F
import numpy as np
from scipy.optimize import brentq
from scipy.integrate import solve_ivp
ARCHIVE=Path(sys.argv[1]) if len(sys.argv)>1 else Path('slac25.omex')
NS={'s':'http://www.sbml.org/sbml/level3/version2/core','e':'http://sbml.org/enzymeml/version2'}

def load():
 assert hashlib.sha256(ARCHIVE.read_bytes()).hexdigest()=='6404d43ced75108a126f1f071057b8600e4aeecefb720c53dc29607bc774afa3'
 z=zipfile.ZipFile(ARCHIVE);root=ET.fromstring(z.read('experiment.xml'))
 pars={p.attrib['id']:float(p.attrib['value']) for p in root.findall('.//s:localParameter',NS)}
 measurements=[]
 for m in root.findall('.//e:measurement',NS):
  idx=int(m.attrib['id'][1:]);a=np.loadtxt(io.BytesIO(z.read(f'data/m{idx}.csv')),delimiter=',')
  initials={x.attrib.get('protein',x.attrib.get('reactant')):float(x.attrib['value']) for x in m.findall('e:initConc',NS)}
  measurements.append({'id':m.attrib['id'],'t':a[:,0],'observed':a[:,1:],'initials':initials})
 return pars,measurements

def reference(t,s0,e0,kcat,km,d):
 # Solve in logarithmic ratio r=log(S/S0), preserving S>0 without clipping.
 exposure=kcat*e0*(-np.expm1(-d*t))/d if d else kcat*e0*t
 if t==0:return s0
 fun=lambda r:s0*np.expm1(r)+km*r+exposure
 r=brentq(fun,-(exposure+s0)/km-1,0,xtol=1e-14,rtol=1e-14)
 return s0*np.exp(r)

def run():
 p,ms=load();rows=[];all_errors=[];nom_errors=[];max_solver_diff=0
 for m in ms:
  t=m['t'];obs=m['observed'];s0=float(obs[0].mean());e0=m['initials']['p0']
  pred=np.array([reference(ti,s0,e0,p['k_cat'],p['K_M'],p['k_ie']) for ti in t])
  nominal=np.array([reference(ti,m['initials']['s1'],e0,p['k_cat'],p['K_M'],p['k_ie']) for ti in t])
  sol=solve_ivp(lambda t,y:[-p['k_cat']*y[1]*y[0]/(p['K_M']+y[0]),-p['k_ie']*y[1]],
      (0,float(t[-1])),[s0,e0],t_eval=t,method='DOP853',rtol=1e-11,atol=1e-12)
  assert sol.success
  diff=float(np.max(abs(sol.y[0]-pred)));max_solver_diff=max(max_solver_diff,diff)
  assert diff<1e-7 and np.all(pred>0) and np.all(np.diff(pred)<=0)
  # t0 contributes to initialization; report residual summary only for t>0.
  err=pred[1:,None]-obs[1:];nomerr=nominal[1:,None]-obs[1:]
  all_errors.extend(err.ravel());nom_errors.extend(nomerr.ravel())
  rows.append({'id':m['id'],'nominal_s0':m['initials']['s1'],'measured_t0_mean':s0,
    'prediction':pred.tolist(),'time_min':t.tolist(),
    'rmse_after_t0_uM':float(np.sqrt(np.mean(err**2))),
    'nominal_initial_rmse_after_t0_uM':float(np.sqrt(np.mean(nomerr**2))),
    'max_abs_residual_after_t0_uM':float(np.max(abs(err))),
    'mean_within_triplicate_sample_sd_uM':float(np.std(obs,axis=1,ddof=1).mean()),
    'max_solver_reference_difference_uM':diff})
 saved=json.loads(Path(__file__).with_name('notebook_25C_saved_MM_curves.json').read_text())
 saved_diff=[]
 for c in saved['curves']:
  m=next(m for m in ms if m['id']==c['inferred_archive_measurement'])
  ref=np.array([reference(ti,float(m['observed'][0].mean()),m['initials']['p0'],p['k_cat'],p['K_M'],p['k_ie']) for ti in c['t']])
  saved_diff.append(float(np.max(abs(ref-np.array(c['S'])))))
 assert max(saved_diff)<1e-6
 # Exact rational budget at archived decimal point parameters.
 z=zipfile.ZipFile(ARCHIVE);root=ET.fromstring(z.read('experiment.xml'))
 pf={q.attrib['id']:F(q.attrib['value']) for q in root.findall('.//s:localParameter',NS)}
 E0f=F('0.073938727');Tf=F(15);hf=F(1,200)
 Vf=pf['k_cat']*E0f;Cf=Vf*(pf['k_ie']+Vf/pf['K_M'])
 budget=Cf*hf*Tf/2
 assert hf<=pf['K_M']/Vf and budget<F(1,100)
 euler_max=0.0
 for m in ms:
  cur_t=0.0;x=float(m['observed'][0].mean());s0=x;e0=m['initials']['p0']
  for target in m['t'][1:]:
   while cur_t<target-1e-13:
    dt=min(float(hf),float(target)-cur_t)
    x-=dt*p['k_cat']*e0*np.exp(-p['k_ie']*cur_t)*x/(p['K_M']+x)
    cur_t+=dt
    assert x>0
   err=abs(x-reference(float(target),s0,e0,p['k_cat'],p['K_M'],p['k_ie']))
   euler_max=max(euler_max,err)
 assert euler_max<float(budget)
 Smax=max(max(m['initials']['s1'],float(m['observed'].max())) for m in ms)
 T=max(float(m['t'][-1]) for m in ms);E0=ms[0]['initials']['p0'];Emin=E0*np.exp(-p['k_ie']*T)
 amax=p['k_cat']*E0/p['K_M'];amin=p['k_cat']*Emin*p['K_M']/(p['K_M']+Smax)**2
 result={'source_sha256':hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),
  'interpretation':'Notebook-declared concentration ODEs in min and uM; not literal SBML; no raw-source modification.',
  'parameters':p,'saved_plot_max_difference_uM':max(saved_diff),'saved_plot_points':800,
  'Euler_scalar_exact_E_test':{'step_min':str(hf),'T_min':str(Tf),'second_derivative_ceiling_exact':str(Cf),'discretization_budget_exact_uM':str(budget),'discretization_budget_uM':float(budget),'observed_max_difference_uM':euler_max,'scope':'Analytical truncation bound at fixed decimal parameters. Floating implementation/exp rounding not certified; conditional model only, not experimental coverage.'},
  'conditions':rows,'pooled_rmse_after_t0_uM':float(np.sqrt(np.mean(np.array(all_errors)**2))),
  'nominal_initial_pooled_rmse_after_t0_uM':float(np.sqrt(np.mean(np.array(nom_errors)**2))),
  'max_solver_reference_difference_uM':max_solver_diff,
  'conditional_derivative_bounds':{'T_min':T,'Smax_uM':Smax,'E0_uM':E0,'Emin_uM':Emin,'a_max_per_min':amax,'a_min_per_min':amin,'sufficient_Euler_step_min':1/amax,'kappa_step_0_1_min':1-0.1*amin},
  'limits':'Floating numerical replay, not interval/Lean certification. Mean measured t0 convention matches saved plotting; residual convention not verified. Same data were used to fit exported parameters; no holdout validation, covariance, calibration propagation or confidence coverage.'}
 return result

if __name__=='__main__':
 r=run();Path(__file__).with_name('declared-model-replay.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
