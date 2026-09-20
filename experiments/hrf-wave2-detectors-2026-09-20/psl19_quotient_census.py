"""Exhaustive normalized maps of the pinned triangle to PSL2(19)."""
import json
from pathlib import Path

q=19
def can(m):
    m=tuple(x%q for x in m)
    s=next(x for x in m if x)
    return tuple(x*pow(s,-1,q)%q for x in m)

def mul(x,y):
    a,b,c,d=x; e,f,g,h=y
    return can((a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h))

def inv(x):
    a,b,c,d=x
    return can((d,-b,-c,a))

def conjugate(g,x):
    return mul(mul(inv(g),x),g)

base=Path(__file__).parent
seed=json.loads((base/'psl19_kernel_result.json').read_text())
xs=[can(m) for m in seed['matrices']]
G=sorted({can((a,b,c,d)) for a in range(q) for b in range(q)
          for c in range(q) for d in range(q) if (a*d-b*c)%q})
assert len(G)==6840
centralizers=[[g for g in G if conjugate(g,x)==x] for x in xs]
assert list(map(len,centralizers))==[20,20,20]
matches=[(u,v) for u in centralizers[0] for v in centralizers[1]
         if conjugate(u,xs[2])==conjugate(v,xs[2])]
u=can((1,5,9,17)); v=can((1,14,12,13))
assert (u,v) in matches
assert conjugate(u,xs[2])!=xs[2]
result={'pgl_order':len(G),'centralizer_orders':list(map(len,centralizers)),
        'normalized_pgl_conjugation_configurations':len(matches),'conjugator_pairs':matches,
        'second_common_edge_image':conjugate(u,xs[2])}
(base/'psl19_quotient_census_result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
