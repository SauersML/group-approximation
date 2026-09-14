# Metabelian skew products: abelian fibres Z/k over cyclic or torus commuting bases.
# Check t <= 2 d(R1) + d(R2) and record the smallest ratios, to see how close the metabelian bound gets.
import itertools, random
R1='bAABaaBAba'; R2='bAAABaaaBAAbaa'; C='abAB'
def inv(P):
    Q=[0]*len(P)
    for i,x in enumerate(P): Q[x]=i
    return Q
def word(wd,A,B):
    M={'a':A,'A':inv(A),'b':B,'B':inv(B)}; cur=list(range(len(A)))
    for ch in reversed(wd):
        P=M[ch]; cur=[P[x] for x in cur]
    return cur
def moved(P): return sum(1 for i,x in enumerate(P) if i!=x)
best={}
viol=0; cnt=0
def test(tag,A,B):
    global viol,cnt
    mc=moved(word(C,A,B))
    if mc==0: return
    m1=moved(word(R1,A,B)); m2=moved(word(R2,A,B)); cnt+=1
    if mc>2*m1+m2:
        viol+=1; print('VIOL',tag,m1,m2,mc)
    r=(max(m1,m2)/mc,(m1+m2)/mc)
    if tag not in best or r<best[tag][0]: best[tag]=(r,m1,m2,mc,len(A))
# cyclic base Z/m, fibre Z/k: (i,x) -> (i+s, x+cfg[i])
for (k,m) in [(2,2),(2,3),(2,4),(3,3),(2,5),(2,6),(3,4)]:
    n=k*m; pts=[(i,x) for i in range(m) for x in range(k)]; idx={p:j for j,p in enumerate(pts)}
    elems=[]
    for s in range(m):
        for cfg in itertools.product(range(k),repeat=m):
            elems.append([idx[((i+s)%m,(x+cfg[i])%k)] for (i,x) in pts])
    pairs=itertools.product(elems,elems) if len(elems)<=400 else ((random.choice(elems),random.choice(elems)) for _ in range(160000))
    for A,B in pairs: test(f'Z{k}wrZ{m}',A,B)
# torus base Z/N x Z/N with fibre Z/k and arbitrary cocycles c,d
random.seed(7)
for (N,k) in [(2,2),(2,3),(3,2),(3,3),(4,2)]:
    pts=[(x,y,i) for x in range(N) for y in range(N) for i in range(k)]; idx={p:j for j,p in enumerate(pts)}
    for trial in range(40000):
        c=[[random.randrange(k) for _ in range(N)] for _ in range(N)]
        d=[[random.randrange(k) for _ in range(N)] for _ in range(N)]
        A=[idx[((x+1)%N,y,(i+c[x][y])%k)] for (x,y,i) in pts]
        B=[idx[(x,(y+1)%N,(i+d[x][y])%k)] for (x,y,i) in pts]
        test(f'torus{N}xZ{k}',A,B)
print('pairs with t>0:',cnt,'violations:',viol)
for tag,v in sorted(best.items()): print(tag,'best (max,sum) ratio',v)
