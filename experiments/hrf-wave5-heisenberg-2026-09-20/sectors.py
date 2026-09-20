"""Exact F8 cocycle ranks for two class-two K7 representation sectors."""
import json,itertools
from pathlib import Path
import numpy as np
P=7
D=Path(__file__).parent
w=json.loads((D/'class_two.json').read_text())
MUL=np.zeros((8,8),dtype=np.uint8)
for a in range(8):
 for b in range(8):
  x=a;y=b;z=0
  while y:
   if y&1:z^=x
   y>>=1;x<<=1
   if x&8:x^=11
  MUL[a,b]=z
INV=np.array([0]+[next(b for b in range(1,8) if MUL[a,b]==1) for a in range(1,8)],dtype=np.uint8)
ROOT=[1]
for i in range(6):ROOT.append(int(MUL[ROOT[-1],2]))
assert len(set(ROOT))==7

def rank(a):
 a=np.array(a,dtype=np.uint8,copy=True);r=0
 for c in range(a.shape[1]):
  inds=np.flatnonzero(a[r:,c])
  if not len(inds):continue
  j=r+int(inds[0]);a[[r,j]]=a[[j,r]]
  a[r]=MUL[INV[a[r,c]],a[r]]
  ids=np.flatnonzero(a[:,c]);ids=ids[ids!=r]
  a[ids]^=MUL[a[ids,c,None],a[r,None,:]]
  r+=1
  if r==a.shape[0]:break
 return r

def mm(a,b):
 out=np.zeros((a.shape[0],b.shape[1]),dtype=np.uint8)
 for k in range(a.shape[1]):out^=MUL[a[:,k,None],b[k,None,:]]
 return out

def inv7(a):
 a=np.array(a,dtype=int);n=len(a);b=np.eye(n,dtype=int)
 for c in range(n):
  j=next(j for j in range(c,n) if a[j,c]);a[[c,j]]=a[[j,c]];b[[c,j]]=b[[j,c]]
  z=pow(int(a[c,c]),-1,7);a[c]=a[c]*z%7;b[c]=b[c]*z%7
  for j in range(n):
   if j!=c:
    z=a[j,c];a[j]=(a[j]-z*a[c])%7;b[j]=(b[j]-z*b[c])%7
 assert np.array_equal(a,np.eye(n,dtype=int))
 return b

def bracket(x,y):
 out=np.zeros(7,dtype=int)
 for t in w['brackets']:out+=(x[t['i']]*y[t['j']]-x[t['j']]*y[t['i']])*np.array(t['value'])
 return out%7

def run(label,central):
 central=np.array(central,dtype=int);om=np.zeros((4,4),dtype=int)
 for t in w['brackets']:
  om[t['i'],t['j']]=np.dot(central,t['value'][4:])%7;om[t['j'],t['i']]=-om[t['i'],t['j']]%7
 def pair(x,y):return int(x@om@y%7)
 rem=list(np.eye(4,dtype=int));basis=[]
 while any(pair(x,y) for x in rem for y in rem):
  i,j=next((i,j) for i,x in enumerate(rem) for j,y in enumerate(rem) if pair(x,y))
  e=rem[i];f=rem[j]*pow(pair(e,rem[j]),-1,7)%7
  basis.extend((e,f));rem=[(v-pair(v,f)*e+pair(v,e)*f)%7 for k,v in enumerate(rem) if k not in(i,j)]
 pairs=len(basis)//2;basis+=rem;trans=inv7(np.array(basis).T)
 points=list(itertools.product(range(7),repeat=pairs));idx={x:i for i,x in enumerate(points)};d=len(points);eye=np.eye(d,dtype=np.uint8)
 def rho(x):
  co=trans@x[:4]%7;p=co[:2*pairs:2];q=co[1:2*pairs:2];z=int(central@x[4:]%7)
  a=np.zeros((d,d),dtype=np.uint8)
  for j,t in enumerate(points):
   dest=tuple((np.array(t)-p)%7);phase=(z-4*int(p@q)+int(q@t))%7;a[idx[dest],j]=ROOT[phase]
  return a
 gens=[np.array(w['vertex_generators'][k],dtype=int) for k in ('U0','V0','U1','V1','U2','V2')]
 # Exhaustive basis BCH representation equations (49 pairs) and finite vertex relations.
 for x in np.eye(7,dtype=int):
  for y in np.eye(7,dtype=int):assert np.array_equal(mm(rho(x),rho(y)),rho((x+y+4*bracket(x,y))%7))
 mats=list(map(rho,gens))
 for a in mats:
  p=eye.copy()
  for _ in range(7):p=mm(p,a)
  assert np.array_equal(p,eye)
 assert not np.any(bracket(gens[0],gens[1]))
 for j in (1,2):
  u,v=gens[2*j:2*j+2];assert not np.any(bracket(u,bracket(u,v))) and not np.any(bracket(v,bracket(u,v)))
 rows=[]
 for i in range(1,7):
  corners=[]
  for j in range(3):
   u,v=gens[2*j:2*j+2];corners.append(rho((i*u-4*i*i*v+(0,-1,1)[j]*pow(12,-1,7)*i**3*bracket(u,v))%7))
  a,b,c=corners;ab=mm(a,b);assert np.array_equal(mm(ab,c),eye)
  rows.append(np.hstack((a^eye,ab^a,eye^ab)))
 constraints=rank(np.vstack(rows))
 fixed=[d-rank(np.vstack((mats[2*j]^eye,mats[2*j+1]^eye))) for j in range(3)]
 global_fixed=d-rank(np.vstack([a^eye for a in mats]))
 h1=2*d-constraints-sum(fixed)+global_fixed
 result=dict(label=label,central_character=central.tolist(),dimension=d,symplectic_rank=2*pairs,face_constraint_rank=constraints,vertex_fixed_dimensions=fixed,global_fixed_dimension=global_fixed,h1_dimension=h1,representation_relations_checked=True)
 print(json.dumps(result),flush=True);return result
results=[run('rank_four_heisenberg',[0,6,0]),run('rank_two_heisenberg',[1,0,0])]
(D/'sector_results.json').write_text(json.dumps(results,indent=2)+'\n')
