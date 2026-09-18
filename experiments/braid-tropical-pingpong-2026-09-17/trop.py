# Tropical (monomial-valuation) spectra of LK images of words in F2=<a,b> < B_4.
import sympy as sp, itertools, math, sys, pickle
from lk import sigma,q,t
N=6
def todict(e):
    e=sp.expand(sp.cancel(e)); d={}
    for term in sp.Add.make_args(e):
        c,rest=term.as_coeff_Mul(); pw=rest.as_powers_dict()
        if rest==1: pw={}
        key=(int(pw.get(q,0)),int(pw.get(t,0)))
        d[key]=d.get(key,0)+int(c)
    return {k:v for k,v in d.items() if v}
def mat(M): return [[todict(M[r,c]) for c in range(N)] for r in range(N)]
def padd(a,b,s=1):
    r=dict(a)
    for k,v in b.items():
        r[k]=r.get(k,0)+s*v
        if r[k]==0: del r[k]
    return r
def pmul(a,b):
    r={}
    for (i,j),u in a.items():
        for (k,l),v in b.items():
            key=(i+k,j+l); r[key]=r.get(key,0)+u*v
    return {k:v for k,v in r.items() if v}
def mmul(A,B):
    C=[[{} for _ in range(N)] for _ in range(N)]
    for i in range(N):
        for k in range(N):
            if not A[i][k]: continue
            for j in range(N):
                if B[k][j]: C[i][j]=padd(C[i][j],pmul(A[i][k],B[k][j]))
    return C
def charpoly(A):
    # Faddeev-LeVerrier: c_N=1, M_1=I, c_{N-k}=-tr(A M_k)/k, M_{k+1}=A M_k + c_{N-k} I
    I=[[{(0,0):1} if i==j else {} for j in range(N)] for i in range(N)]
    M=I; cs={N:{(0,0):1}}
    for k in range(1,N+1):
        AM=mmul(A,M); tr={}
        for i in range(N): tr=padd(tr,AM[i][i])
        c={kk:-v//k for kk,v in tr.items()}
        assert all(v%k==0 for v in tr.values())
        cs[N-k]=c
        M=[[padd(AM[i][j], c if i==j else {}) for j in range(N)] for i in range(N)]
    return cs
S={i:sigma(i,4) for i in (1,2,3)}
Si={i:S[i].inv() for i in (1,2,3)}
a=S[1]*Si[3]; b=S[2]*a*Si[2]
G={'a':mat(a),'A':mat(a.inv()),'b':mat(b),'B':mat(b.inv())}
inv={'a':'A','A':'a','b':'B','B':'b'}
def words(L):
    out=['']
    for _ in range(L):
        out=[w+x for w in out for x in 'aAbB' if not (w and inv[w[-1]]==x)]
    return out
if __name__=='__main__':
    L=int(sys.argv[1]); res={}
    cache={'':[[{(0,0):1} if i==j else {} for j in range(N)] for i in range(N)]}
    for l in range(1,L+1):
        for w in words(l):
            cache[w]=mmul(cache[w[:-1]],G[w[-1]])
            if inv[w[0]]==w[-1]: continue  # not cyclically reduced
            cp=charpoly(cache[w])
            res[w]={k:sorted(v.keys()) for k,v in cp.items()}
        cache={w:m for w,m in cache.items() if len(w)==l}
    pickle.dump(res,open(f'spectra_L{L}.pkl','wb'))
    print(len(res),'cyclically reduced words')
