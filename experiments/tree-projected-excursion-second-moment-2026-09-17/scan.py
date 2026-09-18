from criterion import *
import math
n=2; b=3
TE=terms(3,True)
def pstar(m,v):
    d=4*m+v; lam=v+2*m*math.sqrt(b)
    disc=lam*lam-4*(d-1)
    return 2/(lam+math.sqrt(disc))
def minc(m):
    lo,hi=0.2,0.4
    for _ in range(40):
        mid=(lo+hi)/2
        ok=criterion(TE,n,m,F(mid)/m)[0]
        if ok: hi=mid
        else: lo=mid
    return hi
for m in [3,4,5,6,8,10,15,20,30,40,60,100,200,1000]:
    print(m, round(minc(m),5), round(m*pstar(m,0),5), round(m*pstar(m,2),5))
