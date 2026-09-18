# rank of the incidence vectors of maximum stable sets of the web C_n^k (i~j iff cyclic distance <= k)
import itertools, numpy as np, sys
def web(n,k):
    adj=lambda i,j: 0<min((i-j)%n,(j-i)%n)<=k
    best=[];a=0
    def rec(start,cur):
        nonlocal a,best
        if len(cur)>a: a=len(cur); best=[]
        if len(cur)==a: best.append(tuple(cur))
        for v in range(start,n):
            if all(not adj(v,u) for u in cur): rec(v+1,cur+[v])
    rec(0,[])
    M=np.zeros((len(best),n))
    for r,S in enumerate(best): M[r,list(S)]=1
    return a,len(best),np.linalg.matrix_rank(M)
for k in (2,3,4):
    for n in range(2*k+2,2*k+16):
        a,c,r=web(n,k); print("k",k,"n",n,"alpha",a,"#max",c,"rank",r,"FACET" if r==n else "")
