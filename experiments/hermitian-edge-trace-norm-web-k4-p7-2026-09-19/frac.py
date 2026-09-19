import numpy as np, math, sys
from so2 import *
from rsdp_mod import RobustSDP
RS=RobustSDP(M,E,NS)
rng=np.random.default_rng(5)
def nb(Z): return np.abs(np.linalg.eigvalsh(Z)).max()
for h in [0.3,0.5,0.7,0.9]:
    ns=0; nsd=0; N=40; sdpv=[]
    for t in range(N):
        c=list(rng.uniform(0,2*math.pi,NF)); K0=Kmat(c); lam,U=np.linalg.eigh(K0); Z0=(U*np.sign(lam))@U.conj().T
        if linbound(Z0,c,h)>=TARGET: ns+=1
        v,Z,st=RS.solve([(ci-h,ci+h) for ci in c]); Z=(Z+Z.conj().T)/2
        b=linbound(Z,c,h)/nb(Z); sdpv.append(b)
        if b>=TARGET: nsd+=1
    print("h %.1f sign-closed %d/%d sdp-closed %d/%d sdp median %.2f"%(h,ns,N,nsd,N,np.median(sdpv)),flush=True)
