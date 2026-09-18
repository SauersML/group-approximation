#!/usr/bin/env python3
"""Finite-depth checks for m11-odometer-free-host-is-not-finitely-presented.

Tree: X = {1..11} (coded 0..10), right actions (x w)^g = x^{pi_g} w^{g|_x}.
  alpha = (1,...,11), beta = (1,2,3,4,8)(5,10,7,11,6), M_11 = <alpha, beta>,
  b = (b, alpha, beta, 1, ..., 1),  u = (u, b, beta^-1, 1, ..., 1),  c = (c, b alpha, 1, ..., 1).
An element truncated at depth n is the tuple of images of the 11^n vertices of level n
(vertex x_1...x_n coded as sum x_i 11^(n-i)).  Checks:
 (1) u = c b^-1 at depth 4; b^11 = (b^11, 1, beta, 1, ...) at depth 4 (so (1, beta) lies in the
     image of <b, u> -> R_0 x <beta>);
 (2) b_k = b^(alpha^j) has b at k, alpha at k+1, beta at k+2, and [b_k, b_(k+2)] = [beta, b]@(k+2)
     at depth 4, for every k (indices mod 11);
 (3) [beta, b] is nontrivial, with the first level where it moves a vertex;
 (4) the ray-loop cocycle: for random words w over M_11 u {b, u}^+-1 and points eta = v 1^oo,
     the section of w at the prefix of eta of length max|v_i| + 1 equals, at depth 2, the word
     W_eta(w) built letter by letter from c(b, xi) = b, c(u, xi) = u, c(u, 1^k 2 1^oo) = b;
 (5) the same on relators r of R'' (b^55, u^55, disjoint-support commutators, u = (u,b,beta^-1)
     decomposition): W_eta(r) is trivial at depth 3, as (F1) of the proof requires.
"""
import random

D = 11
def perm_from_cycles(cycles):
    p = list(range(D))
    for cyc in cycles:
        for i, x in enumerate(cyc):
            p[x - 1] = cyc[(i + 1) % len(cyc)] - 1
    return tuple(p)
ALPHA = perm_from_cycles([list(range(1, 12))])
BETA = perm_from_cycles([[1, 2, 3, 4, 8], [5, 10, 7, 11, 6]])

def mul(g, h):             # right action: v^(gh) = (v^g)^h
    return tuple(h[g[v]] for v in range(len(g)))
def inv(g):
    r = [0] * len(g)
    for v, w in enumerate(g): r[w] = v
    return tuple(r)
def ident(n): return tuple(range(D ** n))
def build(root, secs, n):
    """element at depth n from root permutation and list of 11 sections at depth n-1"""
    m = D ** (n - 1); out = [0] * (D ** n)
    for x in range(D):
        s = secs[x]
        for w in range(m):
            out[x * m + w] = root[x] * m + s[w]
    return tuple(out)
def fin(p, n):             # finitary: root p, trivial sections
    return build(p, [ident(n - 1)] * D, n) if n else ident(0)
def section(g, v, n):
    """section of depth-n element g at vertex v (tuple of letters), as depth n-len(v) element"""
    k = len(v); m = D ** (n - k)
    base = sum(x * D ** (k - 1 - i) for i, x in enumerate(v))
    img0 = g[base * m] // m
    return tuple(g[base * m + w] - img0 * m for w in range(m))
def restrict(g, n, k):     # depth-n element to depth k <= n
    m = D ** (n - k)
    return tuple(g[v * m] // m for v in range(D ** k))

_cache = {}
def gen(name, n):
    key = (name, n)
    if key in _cache: return _cache[key]
    I = lambda k: ident(k)
    if n == 0: r = ident(0)
    elif name == 'alpha': r = fin(ALPHA, n)
    elif name == 'beta': r = fin(BETA, n)
    elif name == 'b':
        s = [I(n - 1)] * D; s = list(s)
        s[0] = gen('b', n - 1); s[1] = fin(ALPHA, n - 1); s[2] = fin(BETA, n - 1)
        r = build(tuple(range(D)), s, n)
    elif name == 'u':
        s = list([I(n - 1)] * D)
        s[0] = gen('u', n - 1); s[1] = gen('b', n - 1); s[2] = inv(fin(BETA, n - 1))
        r = build(tuple(range(D)), s, n)
    elif name == 'c':
        s = list([I(n - 1)] * D)
        s[0] = gen('c', n - 1); s[1] = mul(gen('b', n - 1), fin(ALPHA, n - 1))
        r = build(tuple(range(D)), s, n)
    _cache[key] = r
    return r
def word(w, n):
    g = ident(n)
    for name, e in w:
        h = gen(name, n)
        g = mul(g, h if e == 1 else inv(h))
    return g
def comm(g, h): return mul(mul(inv(g), inv(h)), mul(g, h))
def at(g, x, n):           # g@x: g acting below vertex x, depth n (g of depth n-1)
    s = [ident(n - 1)] * D; s = list(s); s[x] = g
    return build(tuple(range(D)), s, n)

def main():
    N = 4
    # (1)
    assert word([('c', 1), ('b', -1)], N) == gen('u', N)
    b11 = word([('b', 1)] * 11, N)
    assert section(b11, (1,), N) == ident(N - 1)
    assert section(b11, (2,), N) == fin(BETA, N - 1)
    assert section(b11, (0,), N) == word([('b', 1)] * 11, N - 1)
    print("(1) u = c b^-1 and b^11 = (b^11, 1, beta, 1, ..., 1) at depth", N)
    # (2)
    b = gen('b', N); a = gen('alpha', N)
    bk = {}
    g = b
    for j in range(D):
        # locate the b-coordinate of g = b^(alpha^j)
        ks = [k for k in range(D) if section(g, (k,), N) == gen('b', N - 1)]
        assert len(ks) == 1
        k = ks[0]
        assert section(g, ((k + 1) % D,), N) == fin(ALPHA, N - 1)
        assert section(g, ((k + 2) % D,), N) == fin(BETA, N - 1)
        assert all(section(g, (x,), N) == ident(N - 1) for x in range(D) if (x - k) % D > 2)
        bk[k] = g
        g = mul(mul(inv(a), g), a)
    assert sorted(bk) == list(range(D))
    cbb = comm(fin(BETA, N - 1), gen('b', N - 1))
    for k in range(D):
        assert comm(bk[k], bk[(k + 2) % D]) == at(cbb, (k + 2) % D, N)
    print("(2) b_k = (b at k, alpha at k+1, beta at k+2) for all 11 k; [b_k, b_(k+2)] = [beta, b]@(k+2)")
    # (3)
    cb = comm(gen('beta', N), gen('b', N))
    lv = min(k for k in range(1, N + 1) if restrict(cb, N, k) != ident(k))
    print("(3) [beta, b] != 1; first level with a moved vertex:", lv)
    # (4) cocycle
    random.seed(1)
    M11 = [ALPHA, BETA]
    letters = [('alpha', 1), ('alpha', -1), ('beta', 1), ('beta', -1), ('b', 1), ('b', -1), ('u', 1), ('u', -1)]
    def cval(l, eta_v):
        """letter c(l, eta) for eta = eta_v 1^oo (eta_v with no trailing 1-letter, coded 0)"""
        name, e = l
        if name in ('alpha', 'beta'): return None
        if len(eta_v) == 0: return (name, e)
        if name == 'u' and all(x == 0 for x in eta_v[:-1]) and eta_v[-1] == 1: return ('b', e)
        return None
    def pinv(p):
        r = [0] * D
        for x in range(D): r[p[x]] = x
        return tuple(r)
    def act_end(l, t, depth=None):
        """image of the end t 1^oo (t without trailing letter 1, coded 0) under letter l"""
        name, e = l
        def strip(t):
            t = list(t)
            while t and t[-1] == 0: t.pop()
            return tuple(t)
        if name in ('alpha', 'beta'):
            p = ALPHA if name == 'alpha' else BETA
            if e == -1: p = pinv(p)
            t = t if t else (0,)
            return strip((p[t[0]],) + tuple(t[1:]))
        if not t: return ()
        x, rest = t[0], tuple(t[1:])
        if name == 'b':
            nxt = {0: ('b', e), 1: ('alpha', e), 2: ('beta', e)}.get(x)
        else:
            nxt = {0: ('u', e), 1: ('b', e), 2: ('beta', -e)}.get(x)
        if nxt is None: return t
        return strip((x,) + act_end(nxt, rest))
    ntest = 0
    for trial in range(3000):
        L = random.randint(1, 6)
        w = [random.choice(letters) for _ in range(L)]
        eta_v = tuple(random.randint(0, 10) for _ in range(random.randint(0, 2)))
        while eta_v and eta_v[-1] == 0: eta_v = eta_v[:-1]
        W = []; cur = eta_v; mx = len(cur)
        for l in w:
            cv = cval(l, cur)
            if cv: W.append(cv)
            cur = act_end(l, cur); mx = max(mx, len(cur))
        depth = 2; m = mx + 1
        if m + depth > 5: continue
        v = tuple(eta_v) + (0,) * (m - len(eta_v))
        n = m + depth
        sec = section(word(w, n), v, n)
        assert sec == word(W, depth), (w, eta_v, W)
        ntest += 1
    print(f"(4) section at the stable prefix equals W_eta(w) at depth 2 on {ntest} random (word, eta) pairs")
    # (5) relators
    rels = {'b^55': [('b', 1)] * 55, 'u^55': [('u', 1)] * 55,
            '[b, u^alpha^3]': [('b', -1), ('alpha', 1), ('alpha', 1), ('alpha', 1), ('u', -1), ('alpha', -1),
                               ('alpha', -1), ('alpha', -1), ('b', 1), ('alpha', 1), ('alpha', 1), ('alpha', 1),
                               ('u', 1), ('alpha', -1), ('alpha', -1), ('alpha', -1)],
            'b^11 (not a relator)': [('b', 1)] * 11}
    for name, r in rels.items():
        triv = word(r, 3) == ident(3)
        vals = set()
        for eta_v in [(), (1,), (0, 1), (0, 0, 1), (2,), (5, 1), (3, 4)]:
            W = []; cur = eta_v
            for l in r:
                cv = cval(l, cur)
                if cv: W.append(cv)
                cur = act_end(l, cur)
            vals.add((eta_v, word(W, 3) == ident(3), len(W)))
        print(f"(5) {name}: trivial at depth 3 = {triv}; (eta, W_eta trivial, |W_eta|):", sorted(vals))
        if triv: assert all(t for _, t, _ in vals)
    print("done")

if __name__ == "__main__":
    main()
