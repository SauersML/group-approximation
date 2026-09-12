from itertools import product, combinations

# Thompson V finite prefix table: dict domain word(str 0/1)->range word

def is_prefix(a,b): return b.startswith(a)

def complete_code_with_leaves(targets):
    targets=set(targets)
    # require pairwise incomparable
    for a in targets:
        for b in targets:
            if a!=b and (is_prefix(a,b) or is_prefix(b,a)):
                raise ValueError((a,b))
    leaves={''}
    changed=True
    while not targets.issubset(leaves):
        # split a leaf that is strict prefix of some target
        found=None
        for l in sorted(leaves,key=len):
            if any(is_prefix(l,t) and l!=t for t in targets):
                found=l; break
        if found is None: raise RuntimeError((leaves,targets))
        leaves.remove(found); leaves.add(found+'0'); leaves.add(found+'1')
    return leaves

def normalize(tab):
    tab=dict(tab)
    while True:
        merged=False
        # find domain sibling pair d0,d1 and range siblings r0,r1 aligned
        keys=set(tab)
        for d0 in sorted(keys,key=lambda x:(-len(x),x)):
            if not d0.endswith('0'): continue
            base=d0[:-1]; d1=base+'1'
            if d1 not in tab: continue
            r0,r1=tab[d0],tab[d1]
            if r0.endswith('0') and r1==r0[:-1]+'1':
                rbase=r0[:-1]
                del tab[d0]; del tab[d1]; tab[base]=rbase
                merged=True; break
        if not merged: return tuple(sorted(tab.items()))

def tabdict(t): return dict(t)

def identity(): return (('', ''),)

def inv(t): return normalize({r:d for d,r in t})

def common_refinement(P,Q):
    # complete prefix codes; least common refinement consists of longer word for each comparable pair
    out=set()
    for p in P:
        for q in Q:
            if is_prefix(p,q): out.add(q)
            elif is_prefix(q,p): out.add(p)
    return out

def refine_range(t, C):
    # C refines range code. returns table with range exactly C
    out={}
    for d,r in t:
        cs=[c for c in C if is_prefix(r,c)]
        for c in cs:
            suffix=c[len(r):]
            out[d+suffix]=c
    assert set(out.values())==set(C)
    return out

def refine_domain(t,C):
    out={}
    for d,r in t:
        cs=[c for c in C if is_prefix(d,c)]
        for c in cs:
            suffix=c[len(d):]
            out[c]=r+suffix
    assert set(out.keys())==set(C)
    return out

def compose(f,g):
    # f o g (apply g, then f)
    F=tabdict(f); G=tabdict(g)
    C=common_refinement(set(G.values()), set(F.keys()))
    gr=refine_range(g,C)
    fr=refine_domain(f,C)
    out={d:fr[c] for d,c in gr.items()}
    return normalize(out)

def mul(f,g):
    # group multiplication convention as function composition f o g
    return compose(f,g)

def powt(f,n):
    if n<0: return powt(inv(f),-n)
    r=identity()
    for _ in range(n): r=mul(r,f)
    return r

def swap_cyl(a,b):
    C=complete_code_with_leaves([a,b])
    out={c:c for c in C}; out[a]=b; out[b]=a
    return normalize(out)

def insert(prefix,f):
    # act f inside cylinder prefix, identity outside. complete prefix code including prefix leaf, replace it by prefixed domain code
    C=complete_code_with_leaves([prefix])
    out={c:c for c in C if c!=prefix}
    for d,r in f:
        out[prefix+d]=prefix+r
    return normalize(out)

def commutator(x,y): return mul(mul(mul(x,y),inv(x)),inv(y))

def eq(x,y): return x==y

def wstr(t): return '{'+', '.join(f'{a or "ε"}->{b or "ε"}' for a,b in t)+'}'

# rootRotation = swap 0/10 * swap 0/11 * swap 0/1 in Lean group multiplication.
# Test both multiplication orientations if needed by relators.
s1=swap_cyl('0','10'); s2=swap_cyl('0','11'); s3=swap_cyl('0','1')
root=mul(mul(s1,s2),s3)
right=insert('1',root)
a=inv(root); b=inv(right)
# relators Commute(a*b^-1, a^-1*b*a), and with a^-2 b a^2
x=mul(a,inv(b)); y1=mul(mul(inv(a),b),a); y2=mul(mul(inv(powt(a,2)),b),powt(a,2))

# word pool canonical V elements from a,b to length radius
gens={'a':a,'A':inv(a),'b':b,'B':inv(b)}
def pool(radius):
    vals={identity():''}
    frontier={identity():''}
    for k in range(radius):
        nxt={}
        for g,w in frontier.items():
            for ch,h in gens.items():
                gh=mul(g,h)
                if gh not in vals:
                    vals[gh]=w+ch; nxt[gh]=w+ch
        frontier=nxt
    return vals

# helper product collision signature for lists S,T

def prod_table(X,Y):
    vals=[]; ids={}
    for i,x in enumerate(X):
        row=[]
        for j,y in enumerate(Y):
            z=mul(x,y)
            if z not in ids: ids[z]=len(ids)
            row.append(ids[z])
        vals.append(row)
    return vals,ids

# brute force binary local rules for small memories. local pattern index bit i corresponds memory element i.
def compose_identity(mu,nu,S,T):
    # sigma o tau identity, sigma memory T, tau S.
    # at e, inner tau at t reads t*s => TS.
    # Build distinct TS coords and index.
    products=[]; idx={}
    for ti,t in enumerate(T):
        for si,s in enumerate(S):
            z=mul(t,s)
            if z not in idx: idx[z]=len(idx); products.append(z)
    e=identity()
    if e not in idx: return False
    eidx=idx[e]
    k=len(products)
    # enumerate patterns
    for bits in range(1<<k):
        nu_in=0
        for ti,t in enumerate(T):
            mu_in=0
            for si,s in enumerate(S):
                z=mul(t,s); bit=(bits>>idx[z])&1
                mu_in |= bit<<si
            out=(mu>>mu_in)&1
            nu_in |= out<<ti
        out=(nu>>nu_in)&1
        target=(bits>>eidx)&1
        if out!=target: return False
    return True

def reverse_nonid(mu,nu,S,T, want_witness=False):
    # tau o sigma; at e inner sigma at s reads s*t => ST
    products=[]; idx={}
    for si,s in enumerate(S):
        for ti,t in enumerate(T):
            z=mul(s,t)
            if z not in idx: idx[z]=len(idx); products.append(z)
    e=identity()
    if e not in idx: return (False,None) if want_witness else False
    eidx=idx[e]; k=len(products)
    for bits in range(1<<k):
        mu_in=0
        for si,s in enumerate(S):
            nu_in=0
            for ti,t in enumerate(T):
                z=mul(s,t); bit=(bits>>idx[z])&1
                nu_in |= bit<<ti
            out=(nu>>nu_in)&1
            mu_in |= out<<si
        out=(mu>>mu_in)&1
        target=(bits>>eidx)&1
        if out!=target:
            return (True,(products,bits)) if want_witness else True
    return (False,None) if want_witness else False

def search_rules(S,T):
    m=len(S); n=len(T)
    mus=range(1<<(1<<m)); nus=range(1<<(1<<n))
    for mu in mus:
        for nu in nus:
            if compose_identity(mu,nu,S,T) and reverse_nonid(mu,nu,S,T):
                return mu,nu,reverse_nonid(mu,nu,S,T,True)
    return None

def sigma_tau_constraints(mu,S,T):
    # returns dict nu_input->required output, or None on conflict
    products=[]; idx={}
    for t in T:
        for s in S:
            z=mul(t,s)
            if z not in idx: idx[z]=len(idx); products.append(z)
    e=identity()
    if e not in idx: return None
    eidx=idx[e]; k=len(products)
    req={}
    # precompute each t row indices in TS
    rows=[[idx[mul(t,s)] for s in S] for t in T]
    for bits in range(1<<k):
        nu_in=0
        for ti,row in enumerate(rows):
            mu_in=0
            for si,j in enumerate(row): mu_in |= ((bits>>j)&1)<<si
            nu_in |= ((mu>>mu_in)&1)<<ti
        target=(bits>>eidx)&1
        old=req.get(nu_in)
        if old is not None and old!=target: return None
        req[nu_in]=target
    return req

def search_rules_fast(S,T):
    m=len(S);n=len(T)
    for mu in range(1<<(1<<m)):
        req=sigma_tau_constraints(mu,S,T)
        if req is None: continue
        free=[i for i in range(1<<n) if i not in req]
        base=sum(v<<i for i,v in req.items())
        for mask in range(1<<len(free)):
            nu=base
            for j,i in enumerate(free): nu |= ((mask>>j)&1)<<i
            if reverse_nonid(mu,nu,S,T):
                return mu,nu,reverse_nonid(mu,nu,S,T,True),req
    return None


def canonical_product_table(X, Y):
    ids = {}
    rows = []
    for x in X:
        row = []
        for y in Y:
            z = mul(x, y)
            if z not in ids:
                ids[z] = len(ids)
            row.append(ids[z])
        rows.append(tuple(row))
    return tuple(rows), len(ids)


def collision_signature(S, T):
    ts, k1 = canonical_product_table(T, S)
    st, k2 = canonical_product_table(S, T)
    assert ts[0][0] == 0 and st[0][0] == 0
    return ts, k1, st, k2


def constraints_compiled(mu, ts, k):
    n = len(ts)
    m = len(ts[0])
    req = {}
    for bits in range(1 << k):
        nu_in = 0
        for ti, row in enumerate(ts):
            mu_in = 0
            for si, j in enumerate(row):
                mu_in |= ((bits >> j) & 1) << si
            nu_in |= ((mu >> mu_in) & 1) << ti
        target = bits & 1  # identity is canonical product-cell 0
        old = req.get(nu_in)
        if old is not None and old != target:
            return None
        req[nu_in] = target
    return req


def reverse_nonidentity_compiled(mu, nu, st, k):
    m = len(st)
    n = len(st[0])
    for bits in range(1 << k):
        mu_in = 0
        for si, row in enumerate(st):
            nu_in = 0
            for ti, j in enumerate(row):
                nu_in |= ((bits >> j) & 1) << ti
            mu_in |= ((nu >> nu_in) & 1) << si
        out = (mu >> mu_in) & 1
        if out != (bits & 1):
            return True
    return False


def solve_signature(z):
    ts, k1, st, k2 = z
    m = len(ts[0])
    n = len(ts)
    for mu in range(1 << (1 << m)):
        req = constraints_compiled(mu, ts, k1)
        if req is None:
            continue
        free = [i for i in range(1 << n) if i not in req]
        base = sum(v << i for i, v in req.items())
        for mask in range(1 << len(free)):
            nu = base
            for j, i in enumerate(free):
                nu |= ((mask >> j) & 1) << i
            if reverse_nonidentity_compiled(mu, nu, st, k2):
                return mu, nu
    return None


def exhaustive_ball(radius, m, n):
    vals = pool(radius)
    e = identity()
    non = [g for g in vals if g != e]
    Sc = list(combinations(non, m - 1))
    Tc = list(combinations(non, n - 1))
    types = {}
    for sc in Sc:
        S = (e,) + sc
        for tc in Tc:
            T = (e,) + tc
            z = collision_signature(S, T)
            types.setdefault(z, (S, T))
    for z, (S, T) in types.items():
        r = solve_signature(z)
        if r is not None:
            return {
                'ok': False,
                'pairs': len(Sc) * len(Tc),
                'types': len(types),
                'S': [vals[x] or 'e' for x in S],
                'T': [vals[x] or 'e' for x in T],
                'rules': r,
            }
    return {'ok': True, 'pairs': len(Sc) * len(Tc), 'types': len(types)}


if __name__ == '__main__':
    assert mul(a, b) != mul(b, a)
    assert mul(x, y1) == mul(y1, x)
    assert mul(x, y2) == mul(y2, x)
    print('rootRotation', wstr(root))
    print('generatorA', wstr(a))
    print('generatorB', wstr(b))
    tests = [(2,2,2), (2,2,3), (2,3,2), (2,3,3),
             (3,2,2), (3,2,3), (3,3,2)]
    for args in tests:
        print(args, exhaustive_ball(*args))
