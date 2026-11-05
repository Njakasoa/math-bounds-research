#!/usr/bin/env python3
"""Read-only descriptive audit of the frozen public SLAC25 OMEX archive.
No data cleaning, model fitting, simulation, or biological validation.
"""
import csv, hashlib, io, json, math, statistics as st, zipfile, sys
from collections import Counter
from pathlib import Path
from xml.etree import ElementTree as ET

SOURCE=Path(sys.argv[1]) if len(sys.argv)>1 else Path('slac25.omex')
OUT=Path(__file__).resolve().parent
NS={'sbml':'http://www.sbml.org/sbml/level3/version2/core','enz':'http://sbml.org/enzymeml/version2','manifest':'http://identifiers.org/combine.specifications/omex-manifest'}
def sha(b): return hashlib.sha256(b).hexdigest()
def stats(a):
    return {'n':len(a),'mean':st.mean(a),'sample_sd':st.stdev(a) if len(a)>1 else None,'min':min(a),'max':max(a)}
original=SOURCE.read_bytes()
report={'audit_date':'2026-11-05','scope':'Descriptive audit only; original archive opened read-only, no raw data modified or excluded.',
'provenance':{'archive_path':'slac25.omex (external original input)','sha256':sha(original),'expected_sha256':'6404d43ced75108a126f1f071057b8600e4aeecefb720c53dc29607bc774afa3','size_bytes':len(original),'dataset_url':'https://doi.org/10.18419/DARUS-3867','file_url':'https://doi.org/10.18419/DARUS-3867/12','license':'CC BY 4.0 according to provided provenance report; not embedded in this archive','dataset_citation':'Max Häussler, DaRUS-3867, version 1, published 2024-01-09, as recorded in provided provenance report','source_of_external_provenance':'Provided report only; no fresh external source fetch in this independent archive audit.'},
'namespaces':NS,'conditions':[],'unit_definitions':[]}
all_values=[]; all_increases=[]; pointwise=[]; condition_summary=[]
with zipfile.ZipFile(io.BytesIO(original)) as z:
    assert z.testzip() is None
    report['members']=[{'name':i.filename,'uncompressed_bytes':i.file_size,'compressed_bytes':i.compress_size,'sha256':sha(z.read(i.filename))} for i in z.infolist()]
    root=ET.fromstring(z.read('experiment.xml'))
    manifest=ET.fromstring(z.read('manifest.xml'))
    report['manifest']=[dict(x.attrib) for x in manifest]
    report['model']={**root.attrib,**root.find('sbml:model',NS).attrib}
    expected_factors={'u0':1e-6,'u1':1e-3,'u2':60,'u3':1,'u4':1e-6,'u5':1/60}
    intended={'u0':'microlitre','u1':'millimole/litre','u2':'minute','u3':'kelvin','u4':'micromole/litre','u5':'1/minute'}
    base={'u0':'litre','u1':'mole/litre','u2':'second','u3':'kelvin','u4':'mole/litre','u5':'1/second'}
    for ud in root.findall('.//sbml:unitDefinition',NS):
        units=[dict(u.attrib) for u in ud.findall('sbml:listOfUnits/sbml:unit',NS)]
        factor=math.prod((float(u['multiplier'])*10**int(u['scale']))**float(u['exponent']) for u in units)
        uid=ud.attrib['id'];expected=expected_factors[uid]
        report['unit_definitions'].append({'id':uid,'name':ud.attrib['name'],'components':units,'literal_factor_in_reference_base':factor,'reference_base':base[uid],'declared_intended_unit':intended[uid],'expected_factor_from_name':expected,'literal_to_named_factor_ratio':factor/expected,'consistent_with_name':math.isclose(factor,expected,rel_tol=1e-12)})
    report['unit_policy']='All tabulated concentration/time numbers are preserved source values labelled by the EnzymeML unit names. Literal SBML scales disagree for u1-u5. No unit repair or SI reinterpretation was silently applied. Resolve this discrepancy before physical-unit or generic SBML-based claims.'
    report['species']=[dict(s.attrib) for s in root.findall('.//sbml:listOfSpecies/sbml:species',NS)]
    report['compartments']=[dict(c.attrib) for c in root.findall('.//sbml:compartment',NS)]
    report['parameters']=[]
    for p in root.findall('.//sbml:localParameter',NS):
        q=dict(p.attrib)
        q.update({el.tag.split('}')[-1]:float(el.text) for el in p.findall('sbml:annotation/enz:parameter/*',NS)})
        q['value']=float(q['value']);report['parameters'].append(q)
    formats={f.attrib['id']:[dict(c.attrib) for c in f.findall('enz:column',NS)] for f in root.findall('.//enz:format',NS)}
    files={f.attrib['id']:dict(f.attrib) for f in root.findall('.//enz:files/enz:file',NS)}
    grids=[]
    for m in root.findall('.//enz:measurement',NS):
        mid=m.attrib['id']; f=files[m.attrib['file']]; path=f['file'].removeprefix('./');schema=formats[f['format']]
        text=z.read(path).decode('utf-8'); raw=list(csv.reader(io.StringIO(text),delimiter=','))
        blank_rows=sum(not row for row in raw); rows=[row for row in raw if row]
        assert all(len(r)==4 for r in rows)
        missing=sum(v.strip()=='' for r in rows for v in r)
        data=[[float(v) for v in r] for r in rows]
        times=[r[0] for r in data];vals=[r[1:] for r in data];flat=[v for r in vals for v in r];all_values+=flat;grids.append(times)
        init=[dict(e.attrib) for e in m.findall('enz:initConc',NS)]
        nominal=float(next(e['value'] for e in init if e.get('reactant')=='s1'))
        reps=[c['replica'] for c in schema if c['type']=='conc'];t0=vals[0]
        changes=[]
        for j,rep in enumerate(reps):
            for i in range(1,len(vals)):
                d=vals[i][j]-vals[i-1][j]
                if d>0: changes.append({'replica':rep,'from_row':i,'to_row':i+1,'from_time':times[i-1],'to_time':times[i],'from_value':vals[i-1][j],'to_value':vals[i][j],'increase':d})
        all_increases += [{'measurement':mid,**r} for r in changes]
        point=[]
        for i,(t,v) in enumerate(zip(times,vals)):
            d=stats(v);d.update({'measurement':mid,'row_1_based':i+1,'time':t,'sample_cv_percent':st.stdev(v)/st.mean(v)*100,'range':max(v)-min(v)})
            point.append(d);pointwise.append(d)
        cond={'measurement':dict(m.attrib),'csv_member':path,'format_id':f['format'],'schema':schema,'csv_header':False,'delimiter':',','blank_rows':blank_rows,'rows':len(rows),'columns':4,'observation_count':len(flat),'replica_labels':reps,'initial_conditions':init,'nominal_abts':nominal,'first_row_time':times[0],'measured_t0_by_replica':dict(zip(reps,t0)),'t0_summary':stats(t0),'t0_mean_minus_nominal':st.mean(t0)-nominal,'t0_mean_relative_difference_percent':100*(st.mean(t0)-nominal)/nominal,'time_grid':times,'time_steps':[b-a for a,b in zip(times,times[1:])],'duplicate_times':len(times)-len(set(times)),'strictly_increasing_time':all(b>a for a,b in zip(times,times[1:])),'missing_cells':missing,'nonfinite_cells':sum(not math.isfinite(v) for r in data for v in r),'negative_concentrations':sum(v<0 for v in flat),'zero_concentrations':sum(v==0 for v in flat),'observation_range':{'min':min(flat),'max':max(flat)},'pointwise_replicate_stats':point,'positive_time_increments':changes,'final_row_summary':stats(vals[-1])}
        report['conditions'].append(cond)
        condition_summary.append({'measurement':mid,'replicas':','.join(reps),'nominal_ABTS_uM_named':nominal,'t0_mean_uM_named':st.mean(t0),'t0_sample_sd_uM_named':st.stdev(t0),'t0_min_uM_named':min(t0),'t0_max_uM_named':max(t0),'t0_mean_minus_nominal_uM_named':st.mean(t0)-nominal,'t0_mean_relative_difference_percent':100*(st.mean(t0)-nominal)/nominal,'final_mean_uM_named':st.mean(vals[-1]),'min_sample_sd_uM_named':min(p['sample_sd'] for p in point),'max_sample_sd_uM_named':max(p['sample_sd'] for p in point),'min_sample_cv_percent':min(p['sample_cv_percent'] for p in point),'max_sample_cv_percent':max(p['sample_cv_percent'] for p in point)})
    report['counts']={'archive_members':len(z.namelist()),'csv_files':len(files),'condition_files':len(report['conditions']),'replicate_trajectories':24,'unique_replicate_labels':len({r for c in report['conditions'] for r in c['replica_labels']}),'rows_per_file':11,'columns_per_file':4,'total_rows':88,'time_values_stored':88,'unique_timepoints':len(set(t for g in grids for t in g)),'observations':len(all_values),'all_numeric_cells_including_time':88*4,'missing_cells':sum(c['missing_cells'] for c in report['conditions']),'nonfinite_cells':sum(c['nonfinite_cells'] for c in report['conditions']),'negative_concentration_values':sum(v<0 for v in all_values),'zero_concentration_values':sum(v==0 for v in all_values),'within_replicate_time_increments':240,'positive_time_increments':len(all_increases),'duplicated_whole_replicate_trajectories':0}
    # Independently verify entire-trajectory duplicate count rather than trusting labels.
    trajectories=[]
    for f in files.values():
        a=[[float(v) for v in row] for row in csv.reader(io.StringIO(z.read(f['file'].removeprefix('./')).decode())) if row]
        trajectories.extend(tuple(r[j] for r in a) for j in (1,2,3))
    report['counts']['duplicated_whole_replicate_trajectories']=len(trajectories)-len(set(trajectories))
    report['time']={'all_files_identical_grid':all(g==grids[0] for g in grids),'source_unit_name':'min','grid':grids[0],'start':min(grids[0]),'end':max(grids[0]),'regular_grid':False,'min_step':min(b-a for a,b in zip(grids[0],grids[0][1:])),'max_step':max(b-a for a,b in zip(grids[0],grids[0][1:])),'median_step':st.median(b-a for a,b in zip(grids[0],grids[0][1:]))}
    report['observed_species']=[{'id':'s1','name':'ABTS','type':'conc','unit_id':'u4','unit_name':'umole / l','xml_isCalculated':'False','note':'The archive provides concentration time courses, not raw absorbance or an independently observed product trajectory. The isCalculated flag is metadata, not proof that calibration/transformation did not occur.'}]
    report['observation_range']={'min':min(all_values),'max':max(all_values)}
    report['positive_time_increments']=all_increases
    m4=[[float(v) for v in r] for r in csv.reader(io.StringIO(z.read('data/m4.csv').decode())) if r]
    m4gap=[r[3]-(r[1]+r[2])/2 for r in m4];abdiff=[abs(r[1]-r[2]) for r in m4]
    report['descriptive_flags']=[{'id':'persistent_C6_offset','measurement':'m4','replica':'C6','rows':11,'direction':'C6 exceeds both A6 and B6 at every timepoint','C6_minus_mean_A6_B6_min':min(m4gap),'C6_minus_mean_A6_B6_max':max(m4gap),'C6_minus_mean_A6_B6_t0':m4gap[0],'C6_minus_mean_A6_B6_final':m4gap[-1],'max_absolute_A6_minus_B6':max(abdiff),'interpretation':'Descriptive candidate for source/calibration review only. Not a proven erroneous observation or justified exclusion; no formal outlier test or deletion.'}]
report['uncertainty_limitations']=[
'Three labelled well trajectories per condition provide only three cross-replicate observations at each time. Whether these represent independent biological preparations is not established by this archive; do not call them biological replicates.',
'Timepoints within each replicate trajectory should not be treated as independent replicates. A shared calibration or plate effects can also correlate replicate wells.',
'CSV concentration columns have no pointwise error, SD, SEM, covariance, detection-limit, or censoring fields. Descriptive sample SD uses n-1=2 degrees of freedom; it is not a deterministic error bound.',
'The archive contains neither raw absorbance, calibration observations/coefficients, nor a fully specified observation transformation. These exist elsewhere according to the provided provenance report and were not independently inspected here.',
'Parameter stdev fields are parameter-estimation metadata, not observation noise. The archive alone does not establish their estimator, sampling distribution, covariance, or confidence level. Optimisation lower/upper bounds are not confidence intervals.',
'Measured t=0 ABTS concentrations differ from nominal initial concentrations. All eight t0 means are below nominal, and 23 of 24 individual t0 values are below nominal; preserve both instead of substituting one for the other.',
'No formal outlier finding is justified by the descriptive screen. Persistent C6 offset and one small non-monotone increment are retained unchanged.',
'Unit-name versus literal-SBML discrepancies must be resolved explicitly before reporting physically interpreted numerical bounds. No concentration/time rescaling was done in this audit.',
'Only s1 is observed. No measured active/inactive-enzyme trajectory, conformation state, oxygen, water, or independent oxidised-product trajectory is provided. Model or biological validation does not follow from these descriptive checks.'
]
report['original_unchanged_after_audit']=sha(SOURCE.read_bytes())==sha(original)
(OUT/'data_audit.json').write_text(json.dumps(report,ensure_ascii=False,indent=2,allow_nan=False)+'\n')
for name, rows in [('condition_summary.csv',condition_summary),('pointwise_replicate_summary.csv',pointwise)]:
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
print(json.dumps({'counts':report['counts'],'time':report['time'],'summary':condition_summary,'positive_time_increments':all_increases,'flags':report['descriptive_flags'],'original_unchanged':report['original_unchanged_after_audit']},indent=2))
