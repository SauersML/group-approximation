# Calibration for gk3-binary-descent-2 (tiny exact checks).
import itertools
# F4 = F2[w]/(w^2+w+1); elements as 2-bit ints (a0 + a1 w)
def f4mul(a,b):
    a0,a1=a&1,a>>1; b0,b1=b&1,b>>1
    c0=(a0*b0 + a1*b1)%2      # w^2 = w+1
    c1=(a0*b1 + a1*b0 + a1*b1)%2
    return c0|(c1<<1)
def matmul(A,B,n):
    C=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s=0
            for k in range(n): s^=f4mul(A[i][k],B[k][j])
            C[i][j]=s
    return C
def span_dim_over_f2(mats,n):
    # each matrix over F4 -> vector over F2 of length 2*n*n
    rows=[]
    for M in mats:
        v=0
        for i in range(n):
            for j in range(n):
                v=(v<<2)|M[i][j]
        rows.append(v)
    basis=[]
    for v in rows:
        for b in basis:
            v=min(v,v^b)
        if v: basis.append(v)
    return len(basis)
def group_images(zeta,r=3):
    n=r
    def t(j):
        M=[[1 if i==k else 0 for k in range(n)] for i in range(n)]
        M[j][j]=zeta
        return M
    C=[[1 if (i==(k+1)%n) else 0 for k in range(n)] for i in range(n)]
    I=[[1 if i==k else 0 for k in range(n)] for i in range(n)]
    gens=[t(j) for j in range(n)]+[C]
    seen={}
    frontier=[I]
    key=lambda M: tuple(tuple(r) for r in M)
    seen[key(I)]=I
    while frontier:
        new=[]
        for M in frontier:
            for g in gens:
                N=matmul(M,g,n)
                if key(N) not in seen:
                    seen[key(N)]=N; new.append(N)
        frontier=new
    return list(seen.values())
imgs=group_images(zeta=2)   # zeta = w, primitive cube root of unity
print('|rho(P)| =',len(imgs),' (P = C3^3 x| C3 has order 81)')
print('F2-dim span rho(P) =',span_dim_over_f2(imgs,3),' target dim_F2 M3(F4) = 18')
ctrl=group_images(zeta=1)
print('control zeta=1: |image| =',len(ctrl),' F2-dim span =',span_dim_over_f2(ctrl,3))
# Split check: G = C2, P = C3, sites G x P; configs 2^6
G=[0,1]; P=[0,1,2]
def act(h,u,x):  # (h,u).x (g,t) = x(h^-1 g, u^-1 t)
    return {(g,t): x[((g-h)%2,(t-u)%3)] for g in G for t in P}
def Theta(x):
    s={g: sum(x[(g,t)] for t in P)%2 for g in G}
    z={g: tuple((x[(g,t)]+s[g])%2 for t in P) for g in G}
    return s,z
ok_bij=set(); ok_eq=True; ok_aug=True
for bits in itertools.product([0,1],repeat=6):
    x={(g,t): bits[2*g*0+g*3+t] for g in G for t in P}
    s,z=Theta(x)
    for g in G:
        if sum(z[g])%2!=0: ok_aug=False
    ok_bij.add((tuple(s[g] for g in G), tuple(z[g] for g in G)))
    for h in G:
        for u in P:
            s2,z2=Theta(act(h,u,x))
            for g in G:
                if s2[g]!=s[(g-h)%2]: ok_eq=False
                if z2[g]!=tuple(z[(g-h)%2][(t-u)%3] for t in P): ok_eq=False
print('split bijective:',len(ok_bij)==64,' augmentation OK:',ok_aug,' equivariant:',ok_eq)
# I_P fixed points under translation for P=C3
fixed=[v for v in itertools.product([0,1],repeat=3) if sum(v)%2==0 and all(v[(t-1)%3]==v[t] for t in P)]
print('P-fixed vectors in I_P:',fixed)
