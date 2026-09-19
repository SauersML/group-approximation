# dedupe an exh file under (th,al,be,ga)~(th+ga,be,ga,al)~(-th,al,ga,be) (conjugation by a rotation,
# inversion), then per class: excision m (<= mmax) first; if none, greedy slit-swap repair (Lmax).
# prints th al be ga rho excess m swapcost nswaps
import sys
from swap import *
from lib import arcx
from excrep import mtab, key
fn=sys.argv[1]; n=int(sys.argv[2]); Lmax=int(sys.argv[3]); mmax=int(sys.argv[4])
def canon(t):
    th,al,be,ga=t; out=[]
    for u in [(th,al,be,ga),((-th)%n,al,ga,be)]:
        for _ in range(3):
            out.append(u); th2,a2,b2,g2=u; u=((th2+g2)%n,b2,g2,a2)
    return min(out)
seen={}
for line in open(fn):
    th,al,be,ga,rho=line.split(); t=canon(tuple(map(int,(th,al,be,ga))))
    seen[t]=max(seen.get(t,0),float(rho))
print('#classes',len(seen),file=sys.stderr)
tab=mtab(n,mmax); b=[(x+1)%n for x in range(n)]
for t,rho in sorted(seen.items(),key=lambda z:z[1]):
    c=arcx(n,*t); ex=excess(b,c.tolist())
    if ex==0: continue
    m=tab.get(key(c)); r=None; ns=0
    if m is None or 2*m+2>rho*3:
        r,lens=greedy(b,c.tolist(),Lmax); ns=len(lens)
    print(*t,'%.3f'%rho,ex,m,r,ns,flush=True)
