"""PSL19 coefficient-three projective generator on cosets of C5."""
from pathlib import Path
import json
base=Path(__file__).parent
ns={}
exec(compile((base.parent.parent/'hrf-wave4-detectors-2026-09-20/borel_a4_homology.py').read_text().split('\nvs=')[0],'audited_cosets','exec'),ns)
G=ns['G']; mul=ns['mul']; inv=ns['inv']; x=ns['xs'][0]; C=set(ns['generate']([x]))
A=sorted(C); assert len(A)==5
labels={}; reps=[]
for g in G:
 if g in labels: continue
 for a in A: labels[mul(g,a)]=len(reps)
 reps.append(g)
assert len(reps)==684
perms=[[labels[mul(x,g)] for g in reps] for x in ns['xs']+[ns['y']]]
data={'prime':3,'group':G,'subgroup':A,'representatives':reps,'permutations':perms,'labels':[labels[g] for g in G],'generators':ns['xs'][:2]}
(base/'module_input.json').write_text(json.dumps(data)+'\n')
