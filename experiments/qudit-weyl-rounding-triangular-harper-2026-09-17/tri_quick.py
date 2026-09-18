import numpy as np
def D(d,a,b):
    w=np.exp(2j*np.pi/d); X=np.roll(np.eye(d),1,axis=0); Z=np.diag(w**np.arange(d))
    return w**((pow(2,-1,d)*a*b)%d)*np.linalg.matrix_power(X,a)@np.linalg.matrix_power(Z,b)
def stab_states(d):
    st=[np.eye(d)[j].astype(complex) for j in range(d)]
    for k in range(d):
        ev,V=np.linalg.eig(D(d,1,k))
        for i in range(d): st.append(V[:,i]/np.linalg.norm(V[:,i]))
    return np.array(st)
for d in [5,7,11,13,31,61,101]:
    st=stab_states(d)
    for sgn in [1,-1]:
      for b in [1,d-1]:
        terms=[(1,D(d,1,0)),(1,D(d,0,1)),(sgn,D(d,1,b))]
        K=sum(c*g+np.conj(c)*g.conj().T for c,g in terms); W=6
        lam=np.linalg.eigvalsh(K)[-1]
        s=max(np.real(np.einsum('si,ij,sj->s',st.conj(),K,st)))
        print(d,sgn,b,"lam=%.5f stab=%.4f c=%.4f"%(lam,s,(lam-s)/(W-lam)),"pred 2d/(pi sqrt3)-1=%.4f"%(2*d/(np.pi*np.sqrt(3))-1), "d/pi-1=%.4f"%(d/np.pi-1), flush=True)
