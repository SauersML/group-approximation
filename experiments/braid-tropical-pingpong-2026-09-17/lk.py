# Lawrence-Krammer rep of B_n (Krammer's formula), exact over Z[q^±,t^±] via sympy.
import sympy as sp, itertools
q,t=sp.symbols('q t')
def pairs(n): return [(j,k) for j in range(1,n+1) for k in range(j+1,n+1)]
def sigma(i,n):
    P=pairs(n); idx={p:r for r,p in enumerate(P)}; N=len(P)
    M=sp.zeros(N,N)
    for (j,k) in P:
        c=idx[(j,k)]
        def add(p,val):
            M[idx[p],c]+=val
        if i not in (j-1,j,k-1,k): add((j,k),1)
        elif i==j-1: add((i,k),q); add((i,j),q**2-q); add((j,k),1-q)
        elif i==j and j!=k-1: add((j+1,k),1)
        elif i==k-1 and i!=j: add((j,i),q); add((j,k),1-q); add((i,k),-(q**2-q)*t)
        elif i==k: add((j,k+1),1)
        elif i==j==k-1: add((j,k),-t*q**2)
    return M
if __name__=='__main__':
    n=4; S=[None]+[sigma(i,n) for i in range(1,n)]
    ok=lambda A:sp.simplify(A)==sp.zeros(*A.shape)
    print('s1s3=s3s1',ok(S[1]*S[3]-S[3]*S[1]))
    for i in (1,2): print('braid',i,ok(S[i]*S[i+1]*S[i]-S[i+1]*S[i]*S[i+1]))
    for i in (1,2,3): print('eig',i,sp.factor(S[i].charpoly(sp.Symbol('x')).as_expr()))
