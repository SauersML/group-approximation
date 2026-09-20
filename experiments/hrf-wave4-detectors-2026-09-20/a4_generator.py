"""Test whether A4 averaging generates F5[PSL2(19)] as a two-sided ideal."""
from pathlib import Path
import json,time
import numpy as np
from flint import nmod_mat
base=Path(__file__).parent; ns={}
exec(compile((base/'borel_a4_homology.py').read_text().split('\nvs=')[0],'audited_cosets','exec'),ns)
G=ns['G']; indices={g:i for i,g in enumerate(G)}
rows=np.zeros((285,3420),dtype=np.int64)
for g,label in ns['labels'].items(): rows[label,indices[g]]=1
perms=[[indices[ns['mul'](g,x)] for g in G] for x in ns['xs'][:2]]
previous=0; steps=[]; start=time.time()
while True:
    R,r=nmod_mat(rows.tolist(),5).rref()
    rows=np.array([[int(R[i,j]) for j in range(3420)] for i in range(r)],dtype=np.int64)
    steps.append(r); print('IDEAL_RANK',r,'seconds',round(time.time()-start,2),flush=True)
    if r==3420 or r==previous: break
    previous=r
    rows=np.concatenate([rows]+[rows[:,np.argsort(perm)] for perm in perms])
result={'coefficient_prime':5,'group_order':3420,'subgroup_order':12,'ideal_ranks':steps,'full_group_algebra':r==3420}
(base/'a4_generator_result.json').write_text(json.dumps(result,indent=2)+'\n')
