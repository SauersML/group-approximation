# Exact integer verification of the chord-weighted Busemann-Schur certificate T(v) <= C v.
# usage: python3 exactschur.py L mode p_num p_den C_num C_den     (mode: rig | tri)
import sys, math, time
from fractions import Fraction
import numpy as np
from schur3 import build_geometry, certify
L=int(sys.argv[1]); mode=sys.argv[2]; a=int(sys.argv[3]); b=int(sys.argv[4]); Cn=int(sys.argv[5]); Cd=int(sys.argv[6])
D={'rig':{1:[0,1,3],2:[0,1,4]}, 'tri':{1:[0,1,1000],2:[0,1,100000]}}[mode]
t0=time.time()
G,NW,src,gis,dst,chd=build_geometry(L,D)
print('mode',mode,'L',L,'windows',NW,'transitions',len(src),'max chords',int(chd.max()),flush=True)
Cf,v=certify(G,NW,src,gis,dst,chd,a/b,iters=600)
print('float certificate C =',Cf,flush=True)
V=[int(math.ceil(x*2**40))+1 for x in v]          # positive integers, V ~ v * 2^40
cmax=int(chd.max())
Wc=[a*(b-a)**c*b**(cmax-c) for c in range(cmax+1)]  # p(1-p)^c * b^(cmax+1)
SP=17320508075688773; SM=17320508075688772; TEN=10**16   # SM/TEN < sqrt3 < SP/TEN
KV=TEN*SM; KD=TEN*TEN; KU=SP*SM                      # common scaling: D = b^(cmax+1)*TEN*SM
letters=[1,-1,2,-2]; li={1:0,-1:1,2:2,-2:3}
tot=[0]*(4*NW)
for s,g,d,c in zip(src.tolist(),gis.tolist(),dst.tolist(),chd.tolist()):
    l=G[g][0]; w=Wc[c]
    for u in letters:
        S=s*4+li[u]
        if l==0: tot[S]+=w*V[d*4+li[u]]*KV
        elif l==u: tot[S]+=w*max(V[d*4+li[u2]] for u2 in letters if u2!=-u)*KU
        else: tot[S]+=w*V[d*4+li[-l]]*KD
Dn=b**(cmax+1)*TEN*SM
ok=all(tot[S]*Cd <= Cn*V[S]*Dn for S in range(4*NW))
worst=max(Fraction(tot[S],V[S]*Dn) for S in range(4*NW))
print('p =',f'{a}/{b}','exact max (Tv)_s/v_s =',float(worst),'<=',f'{Cn}/{Cd}',':',ok,'time',round(time.time()-t0,1),flush=True)
