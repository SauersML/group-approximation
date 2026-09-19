# (a,b)-move test.  [R0] = g - P1 - P2 (P_i = p_i g_c^-1, p_i the prefixes of c in u1, g_c = dEb).
# omega_a, omega_b move mass along left cosets of S_L = kA <bDB, k> (kA)^-1, k = eDDEdd.
# [R0] can be collapsed to a single -h using only omega_a, omega_b iff g P_i^-1 in S_L for some i.
# Necessary test: membership in the image of S_L in finite quotients Q (all homs G->Q).
import sys, numpy as np
from verify_unimodular import U1, G_, inv, tox, fox, fred
from homs import group, evalw
from jtest import homs
k='eDDEdd'; kA=k+'A'
gens=[fred(tox(kA+x+inv(kA))) for x in ('bDB',k)]
P=[fred(p+inv(tox('dEb'))) for s,p in fox(U1,'c')]
tests={'gP1^-1':G_+inv(P[0]),'gP2^-1':G_+inv(P[1]),'P1P2^-1':P[0]+inv(P[1])}
def val(w,Q,x,y):
    return int(evalw(w,Q,np.array([x],dtype=np.int32),np.array([y],dtype=np.int32),np.array([Q['e']],dtype=np.int32))[0])
def closure(Q,gs):
    S={Q['e']}; fr=[Q['e']]
    while fr:
        nw=[]
        for a in fr:
            for g in gs:
                b=int(Q['mul'][a][g])
                if b not in S: S.add(b); nw.append(b)
        fr=nw
    return S
for name in sys.argv[1:]:
    Q=group(name); H=homs(Q); cnt={t:0 for t in tests}; surj=0
    for x,y in H:
        if len(closure(Q,[x,y]))<3: continue
        surj+=1
        S=closure(Q,[val(g,Q,x,y) for g in gens])
        for t,w in tests.items():
            if val(w,Q,x,y) not in S: cnt[t]+=1
    print(name,'homs |im|>=3',surj,'non-member counts',cnt,flush=True)
