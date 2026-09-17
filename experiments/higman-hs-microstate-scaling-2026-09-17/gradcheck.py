import numpy as np
from higman_hs_search import *
rng=np.random.default_rng(1); d=5; k=4; E=edges("cycle",k)
lam=spectrum(d,"roots"); g=[]
for i in range(k):
    W=haar(d,rng); g.append((W*lam)@W.conj().T)
v,S,_=energy_grad(g,E)
for trial in range(3):
    A=[None]*k
    for i in range(k):
        z=rng.standard_normal((d,d))+1j*rng.standard_normal((d,d)); A[i]=(z-z.conj().T)/2
    eps=1e-6
    vp,_,_=energy_grad(conj_step(g,A,eps,set()),E); vm,_,_=energy_grad(conj_step(g,A,-eps,set()),E)
    fd=(vp-vm)/(2*eps)
    an=sum(2*np.trace(A[i]@S[i]).real for i in range(k))
    print(fd, an)
