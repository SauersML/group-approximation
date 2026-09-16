# Referee check (2026-09-16), written independently of cabling.py.
# Target: artifact research/artifacts/zp-loop-braid-descending-links-simply-connected-2026-09-16.md.
# - Lemma 5.1 (cabled McCool generators) for all m <= 7, p != q, k.
#   Cloning is computed letterwise from WZ generator formulas via (CS1):
#   (gh)kappa_k = (g)kappa_{rho(h)k} (h)kappa_k.
#   A_ij is obtained by conjugating A_12 = sigma_1 beta_1 by a permutation braid.
# - Product of clonings: kappa_l then kappa_k equals kappa_k then kappa_{l+1} (k < l), random words.
# - Composite memberships (C1), (C3) of artifact section 6 for n = 6, 7, 8.
# Automorphisms are tuples of reduced words (images of x_1..x_n); composition (f o g)(x) = f(g(x)).
# Run: timeout 600 python3 referee_indep_check.py
import itertools, random
def red(w):
    o=[]
    for a in w:
        if o and o[-1]==-a: o.pop()
        else: o.append(a)
    return tuple(o)
def inv(w): return tuple(-a for a in reversed(w))
def app(f,w):
    o=[]
    for a in w:
        im=f[abs(a)-1] if abs(a)<=len(f) else (abs(a),)
        o.extend(im if a>0 else inv(im))
    return red(o)
def comp(f,g): return tuple(app(f,x) for x in g)   # (f o g)(x_i)=f(g(x_i))
def idn(n): return tuple((i,) for i in range(1,n+1))
# right-action generators phi: x -> x^g ; L(g)=phi_g^{-1}
def L_gen(t,i,e,n):
    f=list(idn(n))
    if t=='s': f[i-1],f[i]=(i+1,),(i,)
    elif e==1: f[i-1]=(i,i+1,-i); f[i]=(i,)        # phi_beta^{-1}
    else: f[i-1]=(i+1,); f[i]=(-(i+1),i,i+1)        # phi_beta
    return tuple(f)
def L(word,n):
    f=idn(n)
    for g in word: f=comp(f,L_gen(*g,n))
    return f
def rg(g,k):
    i=g[1]; return i+1 if k==i else (i if k==i+1 else k)
def cg(g,k):
    t,i,e=g
    if k<i: return [(t,i+1,e)]
    if k==i: return [(t,i,e),(t,i+1,e)]
    if k==i+1: return [(t,i+1,e),(t,i,e)]
    return [(t,i,e)]
def clone(word,k):
    out=[]; idx=k
    for g in reversed(word):
        out=cg(g,idx)+out; idx=rg(g,idx)
    return out
def A(i,j,n):
    f=list(idn(n)); f[i-1]=(j,i,-j); return tuple(f)
def prod(fs,n):
    f=idn(n)
    for g in fs: f=comp(f,g)
    return f
# word for A_ij via conjugating sigma1 beta1 (=A_12) by permutation braid: need word for P_pi
def perm_word(pi,n):
    # pi: dict 1..n -> 1..n ; want word u with L(u)(x_c)=x_{pi c}
    cur=list(range(1,n+1)) # L(u)(x_c)=x_{cur[c-1]}
    word=[]
    target=[pi[c] for c in range(1,n+1)]
    # bubble: composing on the right by s_i swaps images of x_i,x_{i+1}
    arr=cur[:]
    while arr!=target:
        for i in range(n-1):
            # position of arr differ; do bubble sort of target order
            if target.index(arr[i])>target.index(arr[i+1]):
                arr[i],arr[i+1]=arr[i+1],arr[i]; word.append(('s',i+1,1))
    assert L(word,n)==tuple((pi[c],) for c in range(1,n+1)), (pi, L(word,n))
    return word
def Aword(i,j,n):
    rest=[c for c in range(1,n+1) if c not in (i,j)]
    pi={1:i,2:j}; 
    for t,c in enumerate(rest): pi[3+t]=c
    u=perm_word(pi,n); uinv=[('s',g[1],1) for g in reversed(u)]
    w=u+[('s',1,1),('b',1,1)]+uinv
    assert L(w,n)==A(i,j,n)
    return w
hat=lambda k,c: c if c<k else c+1
ok=True; cnt=0
for m in range(2,8):
    n=m+1
    for p in range(1,m+1):
        for q in range(1,m+1):
            if p==q: continue
            w=Aword(p,q,m)
            for k in range(1,m+1):
                c=L(clone(w,k),n)
                if p!=k and q!=k: exp=A(hat(k,p),hat(k,q),n)
                elif q==k: exp=prod([A(hat(k,p),k+1,n),A(hat(k,p),k,n)],n)
                else: exp=prod([A(k,hat(k,q),n),A(k+1,hat(k,q),n)],n)
                cnt+=1
                if c!=exp: ok=False; print("FAIL",m,p,q,k)
print("Lemma 5.1 independent, m<=7:",ok,cnt)
# product of clonings: kappa_l then kappa_k (k<l) vs kappa_k then kappa_{l+1}, on random words
random.seed(1)
ok2=True
for trial in range(300):
    m=random.randint(3,6); n=m+2
    w=[(random.choice('sb'),random.randint(1,m-1),random.choice([1,-1])) for _ in range(random.randint(1,8))]
    w=[(t,i,1 if t=='s' else e) for t,i,e in w]
    k=random.randint(1,m); l=random.randint(k,m)  # need k<l in m-strand indexing? use k<=l
    if k==l: continue
    a=L(clone(clone(w,l),k),n); b=L(clone(clone(w,k),l+1),n)
    if a!=b: ok2=False; print("prod fail",w,k,l)
print("product of clonings kappa_l->kappa_k == kappa_k->kappa_{l+1}:",ok2)
# (C1),(C3) directly: for n=6,7,8 edge {e1,e3} stabilizer contains A_56 ; {e1,e5} contains listed h'
ok3=True
for n in (6,7,8):
    m=n-2
    c=L(clone(clone(Aword(3,4,m),2),1),n)
    ok3 &= (c==A(5,6,n))
    tests={(2,3):[(3,4)],(3,2):[(4,3)],(2,1):[(3,2),(3,1)],(3,1):[(4,2),(4,1)],(1,2):[(1,3),(2,3)],(1,3):[(1,4),(2,4)]}
    for (p,q),exp in tests.items():
        c=L(clone(clone(Aword(p,q,m),4),1),n)
        ok3 &= (c==prod([A(*e,n) for e in exp],n))
print("(C1),(C3) composite memberships n=6,7,8:",ok3)
