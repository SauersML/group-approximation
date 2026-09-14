# Group-level parity obstruction for the level-15 lattice H (see sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts).
# P5 <= SL3(F5), chi = Legendre symbol of det of top-left 2x2 block, K = ker chi.
# sigma = conjugation by M (chi(M)=1). Question: is [M^2] in (1+sigma)(K_ab/2) inside K_ab/2 (an F2-space)?
import itertools
p=5
def mul(A,B): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(3))%p for j in range(3)) for i in range(3))
def inv(A):
    # brute force in group closure later
    return None
I=((1,0,0),(0,1,0),(0,0,1))
gens=[((2,0,0),(0,1,0),(0,0,3)),((1,0,0),(0,2,0),(0,0,3)),((0,1,0),(1,0,0),(0,0,4))]
G={I}; frontier=[I]
while frontier:
    nf=[]
    for g in frontier:
        for s in gens:
            h=mul(g,s)
            if h not in G: G.add(h); nf.append(h)
    frontier=nf
G=sorted(G); print("|P5| =",len(G))
def det2(A): return (A[0][0]*A[1][1]-A[0][1]*A[1][0])%p
squares={(x*x)%p for x in range(1,p)}
def chi(A): return 0 if det2(A) in squares else 1
K=[g for g in G if chi(g)==0]; print("|K| =",len(K))
idx={g:i for i,g in enumerate(G)}
table={(a,b):mul(a,b) for a in G for b in G}
def ginv(a): return next(b for b in G if table[(a,b)]==I)
# derived subgroup of K and squares: Frattini-type quotient V = K/(K^2 [K,K])
def closure(S):
    S=set(S)|{I}; changed=True
    while changed:
        changed=False
        for a in list(S):
            for b in list(S):
                c=table[(a,b)]
                if c not in S: S.add(c); changed=True
    return S
comms=[table[(table[(a,b)],table[(ginv(a),ginv(b))])] for a in K for b in K]
sqs=[table[(a,a)] for a in K]
Phi=closure(comms+sqs)
print("|Phi(K)| =",len(Phi), " dim V = log2(|K|/|Phi|) =", (len(K)//len(Phi)).bit_length()-1)
# cosets of Phi in K
cos={}
reps=[]
for g in K:
    key=frozenset(table[(g,x)] for x in Phi)
    if key not in cos: cos[key]=len(reps); reps.append(g)
def cls(g): return cos[frozenset(table[(g,x)] for x in Phi)]
# V as F2-space: find basis via linear structure: map coset index -> vector by building from generators
n=len(reps)
# group structure on V
vadd={(i,j):cls(table[(reps[i],reps[j])]) for i in range(n) for j in range(n)}
zero=cls(I)
Ms=[g for g in G if chi(g)==1]
results=set()
for M in Ms:
    Minv=ginv(M)
    sig=lambda k: table[(table[(M,k)],Minv)]
    norms={cls(table[(sig(k),k)]) for k in K}   # image of (1+sigma) in V (as a set; it is a subgroup)
    M2=cls(table[(M,M)])
    results.add((M2 in norms, len(norms)))
print("|V| =",n," results over all M with chi(M)=1 (M^2 in image(1+sigma)?, |image|):",results)
# invariant characters theta: V->F2 with theta(sigma v)=theta(v), theta(M^2)=1 exist iff M^2 not in (1+sigma)V
