import itertools
n,r=6,6
u=(2,1,1,1,1,0); b=(2,1,1,1,0,0); w=(0,0,0,0,1,1)
d=lambda a,c: sum(abs(x-y) for x,y in zip(a,c))
nm=lambda a: sum(map(abs,a))
def pos(a):
    nz=[x for x in a if x]; return bool(nz) and nz[-1]>0
L=[p for p in itertools.product(range(-r,r+1),repeat=n) if p[-1]>=0 and nm(p)<=r and pos(p)]
S0=[p for p in L if p!=u and d(p,u)<=r]
blk=[z for z in S0 if not (nm(z)==r and z[-1]==0) and d(z,b)<=r]
lo=[min(0,x,y) for x,y in zip(u,b)]; hi=[max(0,x,y) for x,y in zip(u,b)]; hi[-1]=max(hi[-1],1)
box=[v for v in itertools.product(*[range(a,c+1) for a,c in zip(lo,hi)]) if v in set(S0) and v!=b]
from collections import Counter
cnt=Counter(); ex={}
for v in box:
    zs=[z for z in blk if d(z,v)>r]
    assert zs, v
    # prefer a blocker of a simple form
    z=min(zs,key=lambda z:(nm([x-y for x,y in zip(z,b)]),z))
    ex[v]=z
print(len(box),'candidates, all blocked')
for v,z in sorted(ex.items()): print(v,'blocked by',z,'d(z,b)=',d(z,b),'d(z,v)=',d(z,v))
