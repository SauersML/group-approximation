import sys, itertools
p=5
def read(fn):
    L=open(fn).read().split('\n'); i=0; V=[]
    while i<len(L) and L[i].strip():
        m=int(L[i]); i+=1; v={}
        for _ in range(m):
            w,c=L[i].split(); v[w]=int(c)%p; i+=1
        V.append(v)
    return V
V=read(sys.argv[1]); names=sys.argv[2].split(',')
# express each of the first k vectors in terms of the last 3 (hidden basis)
H=V[-3:]
words=sorted(set().union(*H))
for j,v in enumerate(V[:-3]):
    sol=None
    for co in itertools.product(range(p),repeat=3):
        w={}
        for c,h in zip(co,H):
            for x,y in h.items(): w[x]=(w.get(x,0)+c*y)%p
        w={x:y for x,y in w.items() if y}
        if w==v: sol=co; break
    print(names[j],'=', ' + '.join('%d*%s'%(c,n) for c,n in zip(sol,names[-3:]) if c) if sol else 'NOT in span')
