import numpy as np, sys
from scipy.optimize import linprog
def pts(nr=40,nt=300):
    P=[]
    for r in np.linspace(0,1,nr):
        for t in np.linspace(0,np.pi,nt):
            z=r*np.exp(1j*t)
            if abs(1-z)>1e-3: P.append(z)
    return np.array(P)
P=pts()
def yudin(m,D):
    idx=[(p,q) for p in range(D+1) for q in range(p,D+1)]
    A=np.array([np.real(P**p*np.conj(P)**q) if p==q else np.real(P**p*np.conj(P)**q+np.conj(P**p*np.conj(P)**q)) for (p,q) in idx]).T
    h=1/np.abs(1-P)
    F1=np.array([1.0 if p==q else 2.0 for (p,q) in idx])
    obj=m*F1.copy(); obj[0]-=m*m   # minimize m F(1) - m^2 c00
    bnds=[(None,None)]+[(0,None)]*(len(idx)-1)
    res=linprog(obj,A_ub=A,b_ub=h,bounds=bnds,method='highs')
    return -res.fun,res.x,idx

D=int(sys.argv[1])
for m in range(4,21):
    v,x,idx=yudin(m,D); t=np.sqrt(3)/2*(m-1)**2
    print(m,"Yudin E>=%.4f target %.4f ratio %.4f"%(v,t,v/t),flush=True)
