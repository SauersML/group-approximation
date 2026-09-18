import sys
from functools import lru_cache
def lam1(N,N1,C):
    N2=N//N1; best=10**9
    # (a,b) in Lambda=<(N1,0),(C,N2)>: b=k N2, a = C k + j N1
    for k in range(-N,N+1):
        b=k*N2
        if abs(b)>=best: continue
        a0=(C*k)%N1
        for a in (a0,a0-N1):
            if (a,b)!=(0,0): best=min(best,abs(a)+abs(b))
    return best
mx=0;mn=9;rows=[]
for line in open(sys.argv[1]):
    N,N1,C,g,gg,d,rho,s,t=line.split(); N,N1,C,d=int(N),int(N1),int(C),int(d); rho=float(rho)
    m=min(d,lam1(N,N1,C)); r=m/rho
    if r>mx: mx=r; lmx=line.strip()+" lam1=%d"%lam1(N,N1,C)
    if r<mn: mn=r; lmn=line.strip()+" lam1=%d"%lam1(N,N1,C)
print("max min(|g|,lam1)/rho",mx,lmx); print("min",mn,lmn)
