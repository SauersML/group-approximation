# Free-factor test for f.g. subgroups of F(p,q,r,s): Stallings core graph + Gersten peak reduction
# (a subgroup of rank k is a free factor iff Whitehead moves reduce its core graph to a k-petal rose).
import itertools
LET = 'pqrs'
def _inv(u): return ''.join(c.swapcase() for c in reversed(u))
def _red(u):
    o = []
    for c in u:
        if o and o[-1] == c.swapcase(): o.pop()
        else: o.append(c)
    return ''.join(o)
def core(gens):
    """Folded core graph: returns (nverts, set of edges (v,letter,w) with letter lowercase)."""
    par = [0]; out = [dict()]
    def f(v):
        while par[v] != v: par[v] = par[par[v]]; v = par[v]
        return v
    def new():
        par.append(len(par)); out.append(dict()); return len(par) - 1
    E = []
    for g in gens:
        v = 0
        for i, c in enumerate(g):
            t = 0 if i == len(g) - 1 else new()
            E.append((v, c, t) if c.islower() else (t, c.lower(), v)); v = t
    # fold
    changed = True
    while changed:
        changed = False
        seen = {}
        E = list({(f(a), c, f(b)) for a, c, b in E})
        for a, c, b in E:
            for key, w in (((a, c), b), ((b, c.upper()), a)):
                if key in seen and f(seen[key]) != f(w):
                    x, y = f(seen[key]), f(w); par[max(x, y)] = min(x, y); changed = True
                else: seen[key] = w
        E = list({(f(a), c, f(b)) for a, c, b in E})
    # prune degree-1 vertices other than... (core: prune all hairs, base may move)
    E = set(E)
    while True:
        deg = {}
        for a, c, b in E:
            deg[a] = deg.get(a, 0) + 1; deg[b] = deg.get(b, 0) + 1
        leaves = {v for v, d in deg.items() if d == 1}
        if not leaves: break
        E = {e for e in E if e[0] not in leaves and e[2] not in leaves}
    V = {e[0] for e in E} | {e[2] for e in E}
    return len(V), E
def rank(gens):
    nv, E = core(gens); return len(E) - nv + 1 if E else 0
def whitehead_autos():
    L8 = [c for c in LET] + [c.upper() for c in LET]
    for a in L8:
        others = [c for c in L8 if c.lower() != a.lower()]
        for k in range(1, len(others) + 1):
            for S_ in itertools.combinations(others, k):
                S_ = set(S_)
                m = {}
                for x in LET:
                    w = x
                    if x in S_: w = w + a            # x -> x a
                    if x.upper() in S_: w = _inv(a) + w   # x^-1 -> x^-1 a  i.e. x -> a^-1 x
                    m[x] = w
                yield m
AUT = list(whitehead_autos())
def ap(m, u): return _red(''.join(m[c] if c.islower() else _inv(m[c.lower()]) for c in u))
def size(gens): return len(core(gens)[1])
def reduce_min(gens, verbose=False):
    gens = [g for g in (_red(x) for x in gens) if g]
    s = size(gens)
    while True:
        best = None
        for m in AUT:
            g2 = [ap(m, g) for g in gens]; s2 = size(g2)
            if s2 < s: best = (s2, g2); break
        if not best: return s, gens
        s, gens = best
        if verbose: print('  size', s)
def is_free_factor(gens):
    k = rank(gens); s, g = reduce_min(gens)
    nv, E = core(g)
    return (len(E) == k and nv == 1), k, s
if __name__ == '__main__':
    assert is_free_factor(['pqP', 'rrs'])[0]          # <pqP, rrs> = conj of <q>, ... check
    print(is_free_factor(['pqP', 'rrs']), is_free_factor(['pp']), is_free_factor(['pqPQ']), is_free_factor(['pqrs', 'q']))
def reduce_system(groups):
    """Gersten peak reduction for a finite collection of conjugacy classes of subgroups."""
    groups = [[g for g in (_red(x) for x in G) if g] for G in groups]
    s = sum(size(G) for G in groups)
    while True:
        for m in AUT:
            g2 = [[ap(m, g) for g in G] for G in groups]; s2 = sum(size(G) for G in g2)
            if s2 < s: s, groups = s2, g2; break
        else: return s, groups
def is_ffs(groups):
    """True iff the conjugacy classes of the given subgroups form a free factor system of F_4."""
    s, g = reduce_system(groups)
    ok = all(core(G)[0] == 1 and len(core(G)[1]) == rank(G) for G in g)
    letters = [c for G in g for (_, c, _) in core(G)[1]]
    return ok and len(letters) == len(set(letters)), s
