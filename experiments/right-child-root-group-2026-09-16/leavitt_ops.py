"""Exact arithmetic for elements of R = L_{F_2}(1,2) acting on F_2^(X), X = {0,1}^N.

An element g is stored in canonical form: a dict {w: frozenset(F_w)} where the keys w form a
complete prefix code (leaves of a finite rooted binary tree, '' = the whole space) and
g(delta_{w y}) = sum_{v in F_w} delta_{v y} for every infinite word y.
S[v]T[w] is the prefix replacement w y -> v y.
Canonical form = the coarsest prefix code on whose cylinders g is uniform (unique; see notes).
"""

def canon(g):
    """Merge sibling leaves bottom-up while uniform."""
    g = {w: frozenset(F) for w, F in g.items()}
    changed = True
    while changed:
        changed = False
        # process deepest leaves first
        for w in sorted(g.keys(), key=len, reverse=True):
            if w == '' or w not in g:
                continue
            p = w[:-1]
            a, b = p + '0', p + '1'
            if a in g and b in g:
                Fa, Fb = g[a], g[b]
                if all(v.endswith('0') for v in Fa) and all(v.endswith('1') for v in Fb):
                    Sa = frozenset(v[:-1] for v in Fa)
                    Sb = frozenset(v[:-1] for v in Fb)
                    if Sa == Sb:
                        del g[a]; del g[b]
                        g[p] = Sa
                        changed = True
    return g

def key(g):
    return tuple(sorted((w, tuple(sorted(F))) for w, F in g.items()))

IDENT = {'': frozenset([''])}

def split_leaf(g, w):
    F = g.pop(w)
    g[w + '0'] = frozenset(v + '0' for v in F)
    g[w + '1'] = frozenset(v + '1' for v in F)

def apply_to_word(g, v):
    """Return (list of words) g delta_{v y} as sum of delta_{q y}, if g is uniform along v; else None
    meaning v is a proper prefix of some leaf and must be refined."""
    # find leaf p that is a prefix of v
    for i in range(len(v) + 1):
        p = v[:i]
        if p in g:
            r = v[i:]
            return [q + r for q in g[p]]
    return None

def mul(g, h):
    """(g h)(delta) = g(h(delta))."""
    h = dict(h)
    out = {}
    stack = list(h.keys())
    while stack:
        w = stack.pop()
        if w not in h:
            continue
        acc = {}
        ok = True
        for v in h[w]:
            res = apply_to_word(g, v)
            if res is None:
                ok = False
                break
            for q in res:
                acc[q] = acc.get(q, 0) ^ 1
        if not ok:
            split_leaf(h, w)
            stack.append(w + '0'); stack.append(w + '1')
            continue
        out[w] = frozenset(q for q, c in acc.items() if c)
    return canon(out)

def monomial_sum(terms):
    """terms: list of (v, w) meaning S[v]T[w]; plus identity handled by caller.
    Build element sum_i S[v_i]T[w_i] in canonical form (terms assumed to have w's refinable to a code)."""
    # refine all w to a common complete prefix code: take the set of all w and complete it
    maxlen = max(len(w) for v, w in terms)
    g = {}
    # expand every term to depth maxlen
    import itertools
    for bits in itertools.product('01', repeat=maxlen):
        z = ''.join(bits)
        acc = {}
        for v, w in terms:
            if z.startswith(w):
                q = v + z[len(w):]
                acc[q] = acc.get(q, 0) ^ 1
        g[z] = frozenset(q for q, c in acc.items() if c)
    return canon(g)

def ident_plus(terms):
    return monomial_sum([('', '')] + terms)

def is_ident(g):
    return key(g) == key(IDENT)

def act_vec(g, vec, depth_hint=None):
    """vec: dict word->1 representing sum of delta_{word y} for a fixed generic tail y; words must be
    long enough to be uniform for g. Returns vec."""
    out = {}
    for v in vec:
        res = apply_to_word(g, v)
        if res is None:
            raise ValueError('refine')
        for q in res:
            out[q] = out.get(q, 0) ^ 1
    return {q: 1 for q, c in out.items() if c}

def inverse_bruteforce(g, gens_with_inv=None):
    raise NotImplementedError

def depth(g):
    return max(len(w) for w in g)

def size(g):
    return sum(len(F) for F in g.values())
