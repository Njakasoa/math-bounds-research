"""Check audit and runtime output after rebuild.sh; does not replace Lean."""
from pathlib import Path
import json,re
p=Path(__file__).resolve().parent
expected=json.loads((p/'verification/audit-declarations.json').read_text())
s=(p/'verification/rebuild/AuditEulerError.log').read_text()
assert 'error:' not in s and 'error(' not in s
allowed={'propext','Classical.choice','Quot.sound'}
for d in expected:
    name=d['declaration']
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s)
    empty=re.search(r"'"+re.escape(name)+r"' does not depend on any axioms",s)
    assert m or empty, ('missing audit',name)
    if m:
        axioms={x.strip() for x in m.group(1).split(',') if x.strip()}
        assert axioms<=allowed,(name,axioms)
result={'audited_declarations':len(expected),'allowed_axioms':sorted(allowed),'status':'PASS'}
(p/'verification/FINAL_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
