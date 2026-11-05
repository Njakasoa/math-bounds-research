"""Read-only audit extraction: parses archive/notebook data; executes no source code from either."""
import csv, hashlib, io, json, math, pathlib, statistics, xml.etree.ElementTree as ET, zipfile, sys
from scipy.optimize import brentq
HERE=pathlib.Path(__file__).resolve().parent
ARCH=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else pathlib.Path('slac25.omex')
NS={'s':'http://www.sbml.org/sbml/level3/version2/core','e':'http://sbml.org/enzymeml/version2','m':'http://www.w3.org/1998/Math/MathML'}
z=zipfile.ZipFile(ARCH); root=ET.fromstring(z.read('experiment.xml')); model=root.find('s:model',NS)
out={'archive_sha256':hashlib.sha256(ARCH.read_bytes()).hexdigest(),'archive_file':'slac25.omex (external original input)','model_attributes':model.attrib,
     'units':[], 'species':[], 'compartments':[], 'reactions':[], 'measurements':[]}
for u in model.findall('s:listOfUnitDefinitions/s:unitDefinition',NS):
 parts=[x.attrib for x in u.findall('s:listOfUnits/s:unit',NS)]
 factor=math.prod((float(x['multiplier'])*10**int(x['scale']))**float(x['exponent']) for x in parts)
 out['units'].append({'attributes':u.attrib,'parts':parts,'factor_to_product_of_base_kinds':factor})
for s in model.findall('s:listOfSpecies/s:species',NS):out['species'].append(s.attrib)
for c in model.findall('s:listOfCompartments/s:compartment',NS):out['compartments'].append(c.attrib)
for r in model.findall('s:listOfReactions/s:reaction',NS):
 q={'attributes':r.attrib,'reactants':[x.attrib for x in r.findall('s:listOfReactants/s:speciesReference',NS)],'products':[x.attrib for x in r.findall('s:listOfProducts/s:speciesReference',NS)],'modifiers':[x.attrib for x in r.findall('s:listOfModifiers/s:modifierSpeciesReference',NS)],'local_parameters':[]}
 k=r.find('s:kineticLaw',NS);q['kinetic_law_attributes']=k.attrib;q['mathml']=ET.tostring(k.find('m:math',NS),encoding='unicode')
 for p in k.findall('s:listOfLocalParameters/s:localParameter',NS):
  q['local_parameters'].append({'attributes':p.attrib,'annotations':{e.tag.split('}')[-1]:e.text for e in p.findall('s:annotation/e:parameter/*',NS)}})
 out['reactions'].append(q)
for m in model.findall('.//e:measurement',NS):
 a=[[float(v) for v in row] for row in csv.reader(io.StringIO(z.read('data/'+m.attrib['id']+'.csv').decode()))]
 raw=list(csv.reader(io.StringIO(z.read('data/'+m.attrib['id']+'.csv').decode())))
 out['measurements'].append({'attributes':m.attrib,'initial_conditions':[x.attrib for x in m.findall('e:initConc',NS)],'time_decimal_strings':[row[0] for row in raw],'initial_measured_replicates':a[0][1:],'initial_measured_mean':statistics.mean(a[0][1:]),'rows':len(a),'observations':sum(len(row)-1 for row in a),'initial_sample_standard_deviation':statistics.stdev(a[0][1:])})
out['columns_by_format']={f.attrib['id']:[c.attrib for c in f.findall('e:column',NS)] for f in model.findall('.//e:format',NS)}
out['interpretation']={
 'intended_odes':{'S':'-k_cat*E*S/(K_M+S)','E':'-k_ie*E'},
 'intended_concentration_unit':'micromole/litre','intended_time_unit':'minute',
 'raw_sbml_semantics_do_not_match_intended_odes':True,
 'intended_derivative_mapping':{'r0':'d(s1)/dt','r1':'d(p0)/dt'},
 'observed_species':'s1',
 'reported_stdev_probabilistic_definition':'UNRESOLVED: no full covariance, algorithm or residual/noise model in archive; exact library implementation read was denied',
 'optimizer_bounds_are_confidence_intervals':False,
 'repair_policy':'Preserve archive unchanged. Any concentration-ODE interpretation must be an explicitly labeled derived model, not silently repaired generic SBML.'}
nb=pathlib.Path(sys.argv[2]) if len(sys.argv)>2 else pathlib.Path('slac_kinetics.readonly.ipynb')
assert hashlib.sha256(nb.read_bytes()).hexdigest()=='14d2c07bfc6b07e10e3317bd3176f7b8b1479c0ebe015732b54627235c79e9a8'
j=json.loads(nb.read_text())
plots=[o['data']['application/vnd.plotly.v1+json'] for o in j['cells'][28]['outputs'] if 'application/vnd.plotly.v1+json' in o.get('data',{})]
plot=plots[0];traces=[t for t in plot['data'] if t.get('name')=='michaelis menten with enzyme inactivation']
p={x['attributes']['id']:float(x['attributes']['value']) for r in out['reactions'] for x in r['local_parameters']}
E0=float(out['measurements'][0]['initial_conditions'][0]['value']); k=p['k_cat']; K=p['K_M']; lam=p['k_ie']
all_errors=[]; checks=[]
for m,t in zip(out['measurements'],traces):
 s0=m['initial_measured_mean']; errors=[]
 for tm,recorded in zip(t['x'],t['y']):
  U=k*E0*(-math.expm1(-lam*tm))/lam
  v=s0 if tm==0 else brentq(lambda s:s0-s+K*math.log(s0/s)-U,1e-100,s0,xtol=1e-12)
  errors.append(abs(v-recorded))
 checks.append({'measurement':m['attributes']['id'],'plot_y0':t['y'][0],'observed_t0_mean':s0,'initial_mean_match_abs_error':abs(t['y'][0]-s0),'max_abs_analytical_vs_recorded_plot_error':max(errors),'n_plot_points':len(t['x'])})
 all_errors.extend(errors)
out['notebook_inspection']={'url':'https://raw.githubusercontent.com/EnzymeML/slac_modeling/main/slac_kinetics.ipynb','sha256':hashlib.sha256(nb.read_bytes()).hexdigest(),'executed':False,'relevant_zero_based_cell_indices':{'time_unit':3,'nominal_conditions':7,'blanking':9,'linear_calibration_mapping':11,'remove_200uM':13,'initial_rate_estimation':23,'fixed_parameter_stage':27,'saved_plots':28,'export':38},'estimation_library_pin':'FAIRChemistry/EnzymePynetics@9557beb2da1f9116d08eb0ee996862894a8a37e7','stages':{'stage_1':'fit_models(max_time=3), plain MM k_cat/K_M chosen for stage 2','stage_2':'fit_models_fixed_params(fixed_params=[k_cat,K_M], model=michaelis menten)','export':'explicit MM with enzyme inactivation from init_rate_estimators'},'residual_weighting_or_fitting_initialization':'NOT ESTABLISHED from notebook call sites or saved plots','saved_25C_plot_initialization_checks':checks,'saved_25C_plot_analytical_max_abs_error':max(all_errors),'saved_25C_AIC':{'competitive_product_inhibition_with_inactivation':-514,'exported_MM_with_inactivation':-398},'source_read_denial':{'url':'https://github.com/FAIRChemistry/EnzymePynetics/tree/9557beb2da1f9116d08eb0ee996862894a8a37e7/EnzymePynetics/core','status':'denied: Failed to fetch restricted URL','retry':'none; no alternate route attempted'}}
(HERE/'model_audit_extraction.json').write_text(json.dumps(out,indent=2)+'\n')
curve_output_index=next(i for i,o in enumerate(j['cells'][28]['outputs']) if 'application/vnd.plotly.v1+json' in o.get('data',{}))
(HERE/'notebook_25C_saved_MM_curves.json').write_text(json.dumps({'source_url':out['notebook_inspection']['url'],'source_notebook_sha256':hashlib.sha256(nb.read_bytes()).hexdigest(),'cell_index_zero_based':28,'output_index_zero_based':curve_output_index,'mime_type':'application/vnd.plotly.v1+json','plot_title':plot.get('layout',{}).get('title'),'curves':[{'inferred_archive_measurement':f'm{i}','trace_index_zero_based':next(ti for ti,v in enumerate(plot['data']) if v is t),'label':t.get('name'),'customdata':t.get('customdata'),'t':t['x'],'S':t['y']} for i,t in enumerate(traces)]},indent=2)+'\n')
print(json.dumps({'output':'model_audit_extraction.json','plot_checks':checks,'max_abs_analytical_vs_saved_plot_error':max(all_errors)},indent=2))
