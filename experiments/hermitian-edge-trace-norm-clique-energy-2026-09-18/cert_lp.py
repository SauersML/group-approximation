import numpy as np, sys, json
from scipy.optimize import linprog
def pts(nr=80,nt=720):
    P=[]
    for r in np.linspace(0,1,nr):
        for t in np.linspace(0,np.pi,nt):
            z=r*np.exp(1j*t)
            if abs(1-z)>1e-3: P.append(z)
    return np.array(P)
P=pts()
def lp(m,D,eta):
    idx=[(p,q) for p in range(D+1) for q in range(p,D+1)]
    A=np.array([np.real(P**p*np.conj(P)**q) if p==q else np.real(P**p*np.conj(P)**q+np.conj(P**p*np.conj(P)**q)) for (p,q) in idx]).T
    h=(1-eta)/np.abs(1-P)
    F1=np.array([1.0 if p==q else 2.0 for (p,q) in idx])
    obj=m*F1.copy(); obj[0]-=m*m
    bnds=[(None,None)]+[(0,None)]*(len(idx)-1)
    res=linprog(obj,A_ub=A,b_ub=h,bounds=bnds,method='highs')
    return -res.fun,res.x,idx
if __name__=="__main__":
    m=int(sys.argv[1]); D=int(sys.argv[2]); eta=float(sys.argv[3])
    v,x,idx=lp(m,D,eta); t=np.sqrt(3)/2*(m-1)**2
    print(m,D,eta,"E>=%.5f ratio %.5f"%(v,v/t))
    json.dump({"m":m,"D":D,"eta":eta,"coef":{f"{p},{q}":float(c) for (p,q),c in zip(idx,x)}},open(f"F_m{m}_D{D}.json","w"))
