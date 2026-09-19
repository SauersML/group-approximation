# Exact search: is T = (kA)^-1 g P2^-1 (kA) in S = <beta=bDB, k=eDDEdd> (as a subgroup of G)?
# Meet in the middle over reduced words in beta,k of length <= L on each side; equality via nf in F4 x| Z.
import sys, itertools
from verify_unimodular import U1, G_, inv, tox, fox, fred, nf
L=int(sys.argv[1]) if len(sys.argv)>1 else 7
k='eDDEdd'; kA=k+'A'
P=[fred(p+inv(tox('dEb'))) for s,p in fox(U1,'c')]
idx=int(sys.argv[2]) if len(sys.argv)>2 else 1
T=fred(inv(tox(kA))+G_+inv(P[idx])+tox(kA))
print('T len',len(T),'nf',nf(T)[1])
gen={'p':fred(tox('bDB')),'k':fred(tox(k))}
gen['P']=inv(gen['p']); gen['K']=inv(gen['k'])
def words(L):
    out=[('', '')]; fr=[('', '')]
    for _ in range(L):
        nw=[]
        for s,xw in fr:
            for c in 'pPkK':
                if s and s[-1]==c.swapcase(): continue
                nw.append((s+c, fred(xw+gen[c])))
        out+=nw; fr=nw
    return out
W=words(L); print('words',len(W),flush=True)
left={}
for s,xw in W:
    left.setdefault(nf(fred(inv(xw)+T)),s)   # s^-1 T
for s,xw in W:
    key=nf(xw)
    if key in left:
        print('FOUND T = ',left[key],'*',s); break
else: print('no expression with |s1|,|s2| <=',L)
