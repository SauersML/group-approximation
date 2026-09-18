# Sanity check of the reduction chain on random admissible C:
# ||C||_1 = 2 sum d >= 2 E/(m-1),  |sqrt(d_i d_j) - N_ij| >= |C_ij|,  N PSD with diag d.
import numpy as np
rng=np.random.default_rng(1); worst=1e9; worst2=1e9
for trial in range(3000):
    m=rng.integers(3,9)
    C=np.zeros((m,m),complex)
    for i in range(m):
        for j in range(i+1,m):
            C[i,j]=(1+abs(rng.normal())*rng.integers(0,2))*np.exp(1j*rng.uniform(0,2*np.pi)); C[j,i]=np.conj(C[i,j])
    lam,V=np.linalg.eigh(C)
    A=(V*np.maximum(lam,0))@V.conj().T; B=(V*np.maximum(-lam,0))@V.conj().T
    d=np.real(np.diag(A)); X=np.diag(1/np.sqrt(d))
    N=X@(np.conj(A)*B)@X
    assert np.linalg.eigvalsh(N).min()>-1e-9 and np.allclose(np.real(np.diag(N)),d)
    S=np.sqrt(np.outer(d,d)); G=N/S
    off=~np.eye(m,dtype=bool)
    worst=min(worst,(np.abs(S-N)[off]-np.abs(C)[off]).min())
    E=(1/np.abs(1-G[off])).sum()
    worst2=min(worst2,np.abs(lam).sum()-2*E/(m-1))
print("min(|sqrt(dd)-N|-|C|) =",worst,"  min(||C||_1 - 2E/(m-1)) =",worst2)
