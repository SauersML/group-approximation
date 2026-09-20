"""Exact projective tensor homology, with independently checked GAP summands."""
import json,time
from pathlib import Path
import numpy as np
from flint import nmod_mat
base=Path(__file__).parent
ns={}
exec(compile((base/'borel_a4_homology.py').read_text().split('\nvs=')[0],'audited_cosets','exec'),ns)
perms=[[ns['labels'][ns['mul'](x,g)] for g in ns['representatives']] for x in ns['xs']+[ns['y']]]
mods=json.loads((base/'projective_summands.json').read_text())
assert nmod_mat(sum([m['basis'] for m in mods],[]),5).rank()==285
for m in mods:
    B=np.array(m['basis'],dtype=np.int64)
    for g,perm in zip(m['generators'],perms):
        assert np.array_equal((np.array(g)@B)%5,B[:,np.argsort(perm)])
print('SUMMAND_CERTIFICATE_PASS',flush=True)

def rank(rows): return nmod_mat(rows,5).rank()
def cyclic_basis(g):
    a=len(g); g=np.array(g,dtype=np.int64); eye=np.eye(a,dtype=np.int64)
    N=(g-eye)%5; N4=np.linalg.matrix_power(N,4)%5
    rr,r=nmod_mat(N4.T.tolist(),5).rref(); assert r==a//5
    pivots=[next(j for j in range(a) if rr[i,j]) for i in range(r)]
    out=[]
    for t in pivots:
        row=eye[t]; block=[]
        for k in range(5): block.append(row); row=row@g%5
        assert np.array_equal(row,eye[t]); out.append(block)
    out=np.array(out)
    assert rank(out.reshape(a,a).tolist())==a
    return out
for m in mods:
    m['cyclic']=[cyclic_basis(g) for g in m['generators']]
    d=len(m['basis']); eye=np.eye(d,dtype=np.int64)
    # Row vectors fixed by all Q generators: nullity of stacked transposes.
    m['fixed']=d-rank(np.concatenate([(np.array(g)-eye).T%5 for g in m['generators']]).tolist())

def edge_fixed(A,B):
    rows=[]
    for a in A:
        for b in B:
            for shift in range(5):
                z=sum(np.outer(a[k],b[(k+shift)%5]) for k in range(5))%5
                rows.append(z.ravel().tolist())
    return rows
results=[]; start=time.time()
for i,A in enumerate(mods):
    for j,B in enumerate(mods):
        d=len(A['basis'])*len(B['basis'])
        E=[edge_fixed(A['cyclic'][a],B['cyclic'][b]) for a,b in [(0,0),(1,1),(2,3)]]
        pair=[rank(E[a]+E[b]) for a,b in [(0,1),(0,2),(1,2)]]
        total=rank(sum(E,[]))
        fixed=A['fixed']*B['fixed']
        h1=sum(pair)-total-3*d//5+fixed
        assert h1>=0
        result={'summands':[i,j],'dimension':d,'pair_ranks':pair,'triple_rank':total,'global_fixed':fixed,'h1':h1}
        results.append(result)
        (base/'tensor_homology_result.json').write_text(json.dumps(results,indent=2)+'\n')
        print(json.dumps(result),'seconds',round(time.time()-start,2),flush=True)
