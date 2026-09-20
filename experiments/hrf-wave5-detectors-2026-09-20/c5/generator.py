"""Exact averaging ideal generation test from recorded finite group data."""
from pathlib import Path
import json,time
import numpy as np
from flint import nmod_mat
base=Path(__file__).parent; data=json.loads((base/'module_input.json').read_text()); p=data['prime']
from verify_input import verify
assert verify(data)
G=[tuple(g) for g in data['group']]; indices={g:i for i,g in enumerate(G)}; n=len(G)
def mul(x,y):
 a,b,c,d=x; e,f,g,h=y
 m=tuple(t%19 for t in (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h))
 return min(m,tuple(-t%19 for t in m))
rows=np.zeros((len(data['representatives']),n),dtype=np.int64)
for j,label in enumerate(data['labels']): rows[label,j]=1
perms=[[indices[mul(g,x)] for g in G] for x in data['generators']]
previous=0; steps=[]; start=time.time()
while True:
 R,r=nmod_mat(rows.tolist(),p).rref()
 rows=np.array([[int(R[i,j]) for j in range(n)] for i in range(r)],dtype=np.int64)
 steps.append(r); print('IDEAL_RANK',r,'seconds',round(time.time()-start,2),flush=True)
 if r==n or r==previous: break
 previous=r
 if n-r<=100:
  pivots=[next(j for j,x in enumerate(row) if x) for row in rows]
  free=[j for j in range(n) if j not in set(pivots)]
  assert len(free)==n-r
  residuals=[]
  Rfree=nmod_mat(rows[:,free].tolist(),p)
  for perm in perms:
   translated=rows[:,np.argsort(perm)]
   S=nmod_mat(translated[:,free].tolist(),p)-nmod_mat(translated[:,pivots].tolist(),p)*Rfree
   residuals.extend([[int(S[i,j]) for j in range(len(free))] for i in range(r)])
  rr=nmod_mat(residuals,p).rank()
  print('QUOTIENT_RANK',len(free),rr,flush=True)
  if rr==len(free):
   r=n; steps.append(r); break
 rows=np.concatenate([rows]+[rows[:,np.argsort(perm)] for perm in perms])
(base/'generator_result.json').write_text(json.dumps({'prime':p,'ranks':steps,'full':r==n},indent=2)+'\n')
