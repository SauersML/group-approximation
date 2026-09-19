import collections, itertools
# (2,4,6) triangle group as a reflection group acting on words; use the standard
# faithful matrix representation over exact arithmetic to multiply/compare elements.
# Geometric rep: generators s,t,u with m_st=2, m_su=4, m_tu=6.
import fractions, math
F=fractions.Fraction
# Cartan-like matrix entries: cos(pi/m). pi/2 -> 0; pi/4 -> sqrt2/2; pi/6 -> sqrt3/2.
# Work in the field Q(sqrt2, sqrt3): represent numbers as 4-tuples (a+b*r2+c*r3+d*r6).
def mulnum(x,y):
    a,b,c,d=x; e,f,g,h=y
    return (a*e+2*b*f+3*c*g+6*d*h,
            a*f+b*e+3*c*h+3*d*g,
            a*g+c*e+2*b*h+2*d*f,
            a*h+d*e+b*g+c*f)
def addnum(x,y): return tuple(p+q for p,q in zip(x,y))
def scal(k,x): return tuple(k*p for p in x)
ZERO=(F(0),F(0),F(0),F(0)); ONE=(F(1),F(0),F(0),F(0))
r2=(F(0),F(1),F(0),F(0)); r3=(F(0),F(0),F(1),F(0))
half=lambda x: tuple(p/2 for p in x)
# Gram matrix B(ei,ej) = -cos(pi/m_ij), B(ei,ei)=1
cos={ 'st':ZERO, 'su':half(r2), 'tu':half(r3) }
idx={'s':0,'t':1,'u':2}
Bm=[[ONE if i==j else None for j in range(3)] for i in range(3)]
def setB(a,b,v):
    Bm[idx[a]][idx[b]]=tuple(-p for p in v); Bm[idx[b]][idx[a]]=tuple(-p for p in v)
setB('s','t',cos['st']); setB('s','u',cos['su']); setB('t','u',cos['tu'])
# reflection action on the basis: s_i(e_j) = e_j - 2B(ei,ej) e_i ; matrices 3x3 over the field
def refl(i):
    M=[[ONE if a==b else ZERO for b in range(3)] for a in range(3)]
    for j in range(3):
        # column j: s_i e_j = e_j - 2 B(i,j) e_i
        M[i][j]=addnum(M[i][j], scal(F(-2),Bm[i][j]))
    return tuple(tuple(M[a][b] for b in range(3)) for a in range(3))
def matmul(A,B2):
    return tuple(tuple(functools.reduce(addnum,[mulnum(A[a][k],B2[k][b]) for k in range(3)]) for b in range(3)) for a in range(3))
import functools
GENS={g: refl(idx[g]) for g in 'stu'}
ID=tuple(tuple(ONE if a==b else ZERO for b in range(3)) for a in range(3))
# BFS the group by word length up to L
L=12
elems={ID:('',0)}
frontier=[ID]
length={ID:0}
for l in range(1,L+1):
    nf=[]
    for M in frontier:
        for g in 'stu':
            M2=matmul(GENS[g],M)   # left multiplication
            if M2 not in length:
                length[M2]=l; elems[M2]=(g+elems[M][0],l); nf.append(M2)
    frontier=nf
print("ball sizes up to", L, ":", collections.Counter(length.values())[L], "at top; total", len(length))
# left descent: ell(g w) < ell(w). right descent via transpose word.
def word(M): return elems[M][0]
def lmul(g,M): return matmul(GENS[g],M)
def Ldes(M):
    return {g for g in 'stu' if length.get(lmul(g,M), 10**9) < length[M]}
def Rdes(M):
    # right descent: ell(w g) < ell(w)
    out=set()
    for g in 'stu':
        M2=matmul(M,GENS[g])
        if length.get(M2,10**9) < length[M]: out.add(g)
    return out
# centralizer test: M commutes with GENS[r]
def centralizes(M,r): return matmul(M,GENS[r])==matmul(GENS[r],M)
# CHECK item 3: no w != 1 in C(r) with |L(w)|=2 not containing r... precisely:
# rank-one twisted level needs w in C(r), L(w) = the two OTHER reflections {a,b} = S-{r'}...
# our claim: no w in C_W(r) with L(w) equal to the complement of a single J={s0} where r in J... 
# concretely: J rank one means |L(w)|=2; K={r} needs w in C(r) and r not in L(w)?? r could be in J only if J={r}: then L(w)=S-{r}. Claim: no w!=1 with w in C(r) and L(w)=S-{r0} for the rank-one cases:
viol=0; checked=0
for M,l in length.items():
    if l==0 or l>=L: continue
    Lw=Ldes(M)
    if len(Lw)==2:
        for r in 'stu':
            if centralizes(M,r):
                # J = S - Lw is rank one {j0}; K={r} requires r conjugate-fixed: w in C(r): candidate violation
                # our theorem: impossible when the missing generator j0 satisfies r in J i.e. r == j0? we claimed: for J rank one = {j0}, K={r} forces r=j0?? no: K subset J cap ... K={r} with r in J: J={j0} so r=j0; need w in C(j0) with L(w)=S-{j0}
                j0=(set('stu')-Lw).pop()
                if r==j0:
                    viol+=1; print("VIOLATION item3:", word(M), "r=",r,"L(w)=",Lw)
        checked+=1
print("item3 rank-one twisted check: candidates with |L|=2 checked:",checked,"violations:",viol)
# CHECK item 2: (J,J')-reduced iff minimal in double coset, and min attained
import random
random.seed(1)
Ms=[M for M,l in length.items() if 0<l<L-2]
sub={frozenset(x) for x in [('s',),('t',),('u',),('s','t'),('s','u'),('t','u')]}
def gen_subgroup(J):
    # elements of W_J within the ball
    Js=set(J)
    out={ID}
    fr=[ID]
    while fr:
        nf=[]
        for M in fr:
            for g in Js:
                M2=matmul(GENS[g],M)
                if length.get(M2,10**9)<=L and M2 not in out:
                    out.add(M2); nf.append(M2)
        fr=nf
    return out
subels={J:gen_subgroup(J) for J in sub}
bad2=0; tested=0
for _ in range(300):
    M=random.choice(Ms); J=random.choice(list(sub)); J2=random.choice(list(sub))
    l=length[M]
    # descent criterion for (J,J')-reduced:
    red = all(length[lmul(g,M)]>l for g in J) and all(length[matmul(M,GENS[g])]>l for g in J2)
    # brute-force min of double coset within ball
    best=min((length.get(matmul(matmul(a,M),b),10**9) for a in subels[J] for b in subels[J2]))
    if red and best<l: bad2+=1; print("item2 VIOLATION: reduced but not minimal", word(M), J, J2)
    if (not red) and best>=l: bad2+=1; print("item2 VIOLATION: not reduced but minimal", word(M), J, J2)
    tested+=1
print("item2 double-coset check: tested",tested,"violations:",bad2)
