import sys
inv={'a':'A','A':'a','t':'T','T':'t'}
def I(w): return ''.join(inv[c] for c in reversed(w))
for line in open(sys.argv[1]):
    w=line.split()[0]; L=len(w)
    cps=[w[i:]+w[:i] for i in range(L)]+[I(w)[i:]+I(w)[:i] for i in range(L)]
    best=0
    for i,u in enumerate(cps):
        for j,v in enumerate(cps):
            if i==j: continue
            k=0
            while k<L and u[k]==v[k]: k+=1
            best=max(best,k)
    print(w,'maxpiece',best,'len',L)
