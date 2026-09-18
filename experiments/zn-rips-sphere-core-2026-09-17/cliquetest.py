import itertools, sys
n=int(sys.argv[1]); r=int(sys.argv[2])
def pos(y):
    for v in reversed(y):
        if v: return v>0
    return False
def d(a,b): return sum(abs(p-q) for p,q in zip(a,b))
pts=[y for y in itertools.product(range(-r,r+1),repeat=n) if sum(map(abs,y))<=r and pos(y)]
S=[y for y in pts if sum(map(abs,y))==r]; V=[y for y in pts if sum(map(abs,y))<r]
idx={y:i for i,y in enumerate(S)}
adj=[set(j for j,z in enumerate(S) if j!=i and d(y,z)<=r) for i,y in enumerate(S)]
def collapse(W):
    W=set(W)
    changed=True
    while changed:
        changed=False
        for y in sorted(W,key=lambda t:-sum(map(abs,t))):
            Ny=[z for z in W if d(y,z)<=r]
            for w in Ny:
                if w!=y and all(d(w,z)<=r for z in Ny):
                    W.discard(y); changed=True; break
    return W
def issimplex(W):
    return len(W)>0 and all(d(a,b)<=r for a,b in itertools.combinations(W,2))
cnt=0; bad=0; maxk=0
def meetpos(tau):
    for k in range(n):
        if all(S[i][k]>0 for i in tau): return True
    return False
def rec(tau,cand):
    global cnt,bad,maxk
    if tau:
        cnt+=1; maxk=max(maxk,len(tau))
        if not meetpos(tau):
            W=[y for y in V if all(d(y,S[i])<=r for i in tau)]
            K=collapse(W)
            if not issimplex(K):
                bad+=1
                if bad<=5: print("bad clique",[S[i] for i in tau],"W",len(W),"K",len(K))
    for j in sorted(cand):
        if not tau or j>tau[-1]:
            rec(tau+[j], cand & adj[j])
rec([], set(range(len(S))))
print(f"n={n} r={r} |S+|={len(S)} cliques={cnt} maxclique={maxk} bad={bad}")
