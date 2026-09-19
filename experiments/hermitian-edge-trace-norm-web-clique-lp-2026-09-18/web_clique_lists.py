# Exact exception lists for the clique-window route on the webs C_n^k (m = k+1), given a certified
# rational lower bound L_m <= c(K_m).  The n windows {t..t+k} are cliques K_m covering each vertex m
# times, so ||C||_1 >= (n/m) c(K_m).  (R_{n,k}) follows iff (n L_m/m)^2 >= 3 (n - floor(n/m))^2.
# L_m = 2 (c00 m^2 - m F(1))/(m-1) from a verified Yudin certificate F (verify.py log), or given directly.
import json, sys
from fractions import Fraction as Fr
def L_from_F(fn,m,scale=10**7):
    J=json.load(open(fn)); C={}
    for k,v in J["coef"].items():
        p,q=map(int,k.split(",")); c=Fr(round(v*scale),scale)
        if (p,q)!=(0,0) and c<0: c=Fr(0)
        if c!=0: C[(p,q)]=c
    F1=sum(c*(1 if p==q else 2) for (p,q),c in C.items()); c00=C.get((0,0),Fr(0))
    return 2*(c00*m*m-m*F1)/(m-1)
sU=Fr(17320509,10**7); assert sU*sU>3
def exceptions(m,L):
    k=m-1; eps=L-(m-1)*sU        # eps <= c_m - sqrt3 (m-1)
    assert eps>0
    N=int((m-1)*sU/eps)+2          # for n >= N: n eps >= sqrt3 (m-1) >= sqrt3 r, so (R) holds
    bad=[]
    for n in range(2*k+2,max(N,2*k+3)):
        q=n//m; lhs=n*L/m
        if not (lhs>0 and lhs*lhs>=3*(n-q)**2): bad.append(n)
    return float(eps),N,bad
if __name__=="__main__":
    for arg in sys.argv[1:]:
        m,src=arg.split(":"); m=int(m)
        L=L_from_F(src,m) if src.endswith(".json") else Fr(src)
        eps,N,bad=exceptions(m,L)
        print("k=%d m=%d L_m=%.6f eps_m>=%.5f all n>=%d pass; exceptions n>=2k+2: %s"%(m-1,m,float(L),eps,N,bad))
