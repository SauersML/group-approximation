"""Check of the frame obstruction for the cross-slit pair on (Z/p)^2 x Z/2 with P=(0,0), Q=(0,h):
b(x,e)=(x+e1, e+[x=P]), c(x,e)=(x+e2, e+[x=Q]).  For every primitive v with |v1|+|v2|<=p-1,
B=b^v1 c^v2 (c first) must have a nonempty union M_B of 2p-cycles, and M_B != c(M_B) when v1!=0,
M_B != b(M_B) when v1=0.  Then any commuting (b'',c'') with b''^v1 c''^v2 = B has
max(rank(b''-b),rank(c''-c)) >= p (proof in the -proof.md).  Also prints the exact profile.
usage: python3 crossframes.py p"""
import sys
from math import gcd
import numpy as np
from perm import *
p=int(sys.argv[1]); h=(p-1)//2
idx=lambda x1,x2,e: ((x2%p)*p+(x1%p))*2+e
n=2*p*p; b=np.empty(n,int); c=np.empty(n,int)
for x1 in range(p):
    for x2 in range(p):
        for e in (0,1):
            b[idx(x1,x2,e)]=idx(x1+1,x2,e^(1 if (x1,x2)==(0,0) else 0))
            c[idx(x1,x2,e)]=idx(x1,x2+1,e^(1 if (x1,x2)==(0,h) else 0))
checked=0; bad=[]
for v1 in range(-(p-1),p):
    for v2 in range(-(p-1),p):
        if (v1,v2)==(0,0) or abs(v1)+abs(v2)>p-1 or gcd(abs(v1),abs(v2))!=1: continue
        B=word(b,c,v1,v2)
        M=set(); lens=set()
        for cy in cycles_of(B):
            lens.add(len(cy))
            if len(cy)==2*p: M.update(cy)
        assert lens<= {p,2*p}, lens
        g=c if v1!=0 else b
        gM=set(int(g[z]) for z in M)
        ok = len(M)>0 and gM!=M and len(M-gM)>=2*p
        checked+=1
        if not ok: bad.append((v1,v2,len(M)))
print('p',p,'h',h,'frames checked',checked,'failures',bad)
print('profile',profile(b,c))
