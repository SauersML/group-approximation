import itertools, sys
def inv(c): return c.swapcase()
def red(w):
    s=[]
    for c in w:
        if s and s[-1]==inv(c): s.pop()
        else: s.append(c)
    # cyclic
    i=0; j=len(s)
    while j-i>1 and s[i]==inv(s[j-1]): i+=1; j-=1
    return ''.join(s[i:j])
def canon(w):
    rots=[w[i:]+w[:i] for i in range(len(w))]
    wi=''.join(inv(c) for c in reversed(w))
    rots+=[wi[i:]+wi[:i] for i in range(len(wi))]
    return min(rots)
G="xyz"
def whs():
    out=[]
    for a in "xyzXYZ":
        others=[g for g in G if g!=a.lower()]
        for opts in itertools.product(range(4),repeat=2):
            if opts==(0,0): continue
            m={}
            for g,o in zip(others,opts):
                img=[g, a+g, g+inv(a), a+g+inv(a)][o]
                m[g]=img; m[inv(g)]=''.join(inv(c) for c in reversed(img))
            m[a.lower()]=a.lower(); m[a.upper()]=a.upper()
            out.append(m)
    return out
W=whs()
def apply(m,w): return red(''.join(m[c] for c in w))
w=red(sys.argv[1]); L=len(w)
# reduce to minimal
changed=True
while changed:
    changed=False
    for m in W:
        u=apply(m,w)
        if len(u)<len(w): w=u; changed=True; break
print("minimal length", len(w), w)
seen={canon(w)}; fr=[w]
while fr:
    nf=[]
    for u in fr:
        for m in W:
            v=apply(m,u)
            if len(v)==len(w):
                c=canon(v)
                if c not in seen: seen.add(c); nf.append(v)
            elif len(v)<len(w): print("not minimal!", v); sys.exit()
    fr=nf
sup=[s for s in seen if len(set(s.lower()))<3]
print("minimal set size", len(seen), "missing a generator:", len(sup), sup[:5])
