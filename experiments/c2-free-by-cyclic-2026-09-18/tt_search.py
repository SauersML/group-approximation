import itertools, sys
L='pqrs'
def inv(u): return u[::-1].swapcase()
def red(u):
    st=[]
    for c in u:
        if st and st[-1]==c.swapcase(): st.pop()
        else: st.append(c)
    return ''.join(st)
def app(m,u): return red(''.join(m[c] if c.islower() else inv(m[c.lower()]) for c in u))
def comp(m1,m2): # m1 after m2
    return {c: app(m1, m2[c]) for c in L}
def invert(m):
    # brute: use known inverse pairs only via tracking
    raise
PHI={'p':'q','q':'r','r':'s','s':'rrSqPRs'}
PHII={'q':'p','r':'q','s':'r','p':'QrSqqRp'}
# elementary Nielsen moves and inverses
gens=[]
for a in L:
    for b in L:
        if a==b: continue
        for sa in (a,a.upper()):
            for sb in (b, b.upper()):
                # a -> a*b  (sa, sb choose sides): right mult and left mult
                m={c:c for c in L}; m[a]=red(a+sb); mi={c:c for c in L}; mi[a]=red(a+inv(sb)); gens.append((m,mi))
                m={c:c for c in L}; m[a]=red(sb+a); mi={c:c for c in L}; mi[a]=red(inv(sb)+a); gens.append((m,mi))
# dedupe
seen=set(); G2=[]
for m,mi in gens:
    k=tuple(m[c] for c in L)
    if k not in seen: seen.add(k); G2.append((m,mi))
gens=G2
def Dmap(m):
    d={}
    for c in L:
        d[c]=m[c][0]; d[c.upper()]=inv(m[c])[0]
    return d
def is_tt(m):
    if any(len(m[c])==0 for c in L): return False
    d=Dmap(m); dirs=list(d)
    # gates: x~y iff D^k x == D^k y for some k (k<=16)
    def orb(x):
        o=[x]
        for _ in range(16): x=d[x]; o.append(x)
        return o
    O={x:orb(x) for x in dirs}
    def illegal(x,y): return any(O[x][k]==O[y][k] for k in range(17))
    for c in L:
        w=m[c]
        for i in range(len(w)-1):
            x=w[i].swapcase(); y=w[i+1]  # turn at vertex between: incoming end of w[i] = direction inv, and outgoing w[i+1]
            if illegal(x,y): return False
    return True
def size(m): return sum(len(m[c]) for c in L)
best=[]
start=[(PHII,'phi^-1'),(PHI,'phi')]
for base,name in start:
    frontier=[({c:c for c in L},{c:c for c in L},'')]
    found=0
    for depth in range(int(sys.argv[1])+1):
        newf=[]
        for th,thi,desc in frontier:
            conj=comp(th,comp(base,thi))
            if is_tt(conj):
                found+=1
                if found<=5: print(name,'depth',depth,'size',size(conj),conj,desc,flush=True)
            if depth<int(sys.argv[1]):
                for gi,(g,gv) in enumerate(gens):
                    newf.append((comp(g,th),comp(thi,gv),desc+str(gi)+','))
        frontier=newf
        print(name,'depth',depth,'done, found',found,'frontier',len(frontier),flush=True)
