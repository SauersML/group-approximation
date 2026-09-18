# Obstruction check for top-sphere-first deletion on Lmax = L([-r,r]^{n-1} x [0,r]).
# Deletes the balanced sphere points, then in rounds deletes every unbalanced sphere point x having ANY
# y in hull(0,x), y > 0, y != x, with N[x] ∩ C ⊆ N[y] for the full current set C (all norms). Rounds are
# the maximal closure, since domination is monotone in C. Usage: python3 hull_rounds.py n r
import itertools, sys
n,r=int(sys.argv[1]),int(sys.argv[2])
def norm(v): return sum(map(abs,v))
def d(a,b): return sum(abs(x-y) for x,y in zip(a,b))
def pos(v):
    for a in reversed(v):
        if a: return a>0
    return False
def bal(x,y):
    s=[i for i in range(len(x)) if x[i]]
    for sg in itertools.product([1,-1],repeat=len(s)):
        a=sum(g*abs(x[i]) for g,i in zip(sg,s)); b=sum(g*abs(y[i]) for g,i in zip(sg,s))
        if b>max(0,a) or b<min(0,a): return False
    return True
L=[v for v in itertools.product(range(-r,r+1),repeat=n) if norm(v)<=r and pos(v)]
def hull(x):
    return [y for y in itertools.product(*[range(min(0,a),max(0,a)+1) for a in x]) if y!=x and any(y) and pos(y)]
sph=[x for x in L if norm(x)==r]
unb=set(x for x in sph if not any(bal(x,y) for y in hull(x)))
cur=set(L)-(set(sph)-unb)
print(f"n={n} r={r} |Lmax|={len(L)} sphere={len(sph)} unbalanced={len(unb)}")
rnd=0
while unb:
    dele=[]
    for x in list(unb):
        N=[z for z in cur if d(z,x)<=r]
        if any(all(d(z,y)<=r for z in N) for y in hull(x)): dele.append(x)
    rnd+=1; print(f"  round {rnd}: deleted {len(dele)} of {len(unb)}")
    if not dele: break
    for x in dele: unb.discard(x); cur.discard(x)
print(f"n={n} r={r} never-deleted={len(unb)} examples={sorted(unb)[:3]}")
