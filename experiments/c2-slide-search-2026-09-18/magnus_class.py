# Module-level condition for the Magnus (c-elimination) family.
from verify_unimodular import BAS, U0, U1, G_, D, inv, fred, ring, fox, rmul
def add(A,B,s=1):
    o=dict(A)
    for k,v in B.items(): o[k]=o.get(k,0)+s*v
    return {k:v for k,v in o.items() if v}
du0={z:ring(fox(U0,z)) for z in 'abcde'}
cz={z:ring([(s,G_+u) for s,u in fox(U0,z)]+[(-s,u) for s,u in fox(U1,z)]) for z in 'abcde'}
s={}
for z in 'abcde': s=add(s,rmul(du0[z],ring(D[z])))
print('s = du0 . d =',s)
for z in 'abcde': print(z,'du0',du0[z])
from verify_unimodular import fromfib
def gw(k):  # group element key -> x,y word
    u,m=k; return fromfib(u)+('y'*m if m>0 else 'Y'*(-m))
def ginv(k): return ring([(1,inv(gw(k)))])
(kc,vc),=du0['c'].items()
kap=rmul(cz['c'],{k:v*vc for k,v in ginv(kc).items()})
cp={z:add(cz[z],rmul(kap,du0[z]),-1) for z in 'abcde'}
for z in 'abcde': print(z,'c\'',len(cp[z]),'aug',sum(cp[z].values()), cp[z] if len(cp[z])<6 else '')
print('kappa',len(kap),sum(kap.values()))
