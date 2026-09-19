#!/usr/bin/env python3
"""Finite-depth checks for m11-separated-loop-host-has-b1-one.

Tree: X = {1..11} (coded 0..10), right actions (x w)^g = x^{pi_g} w^{g|_x}.
  alpha = (1,...,11), beta = (1,2,3,4,8)(5,10,7,11,6), M_11 = <alpha, beta>,
  b = (b, alpha, beta, 1, ..., 1),  ba := b alpha = (b, alpha, beta, 1, ..., 1) alpha,
  c' = (1, 1, 1, c', b alpha, 1, ..., 1)   (c' at letter 4, b alpha at letter 5).
Checks:
 (1) c' ((b alpha)@5)^-1 = c'@4 at depth 4 (so c'@4 lies in R' = <M_11, b, c'>);
 (2) c'^m has section c'^m at 4 and (b alpha)^m at 5, trivial elsewhere, m = 1..12, depth 3;
     (b alpha)^m is nontrivial at depth 3 for m = 1..30 (its infinite order is proved by hand);
 (3) the loop cocycle at 4^infinity: for random words w over {alpha, beta, b, c'}^+-1 and ends
     eta = t 4^oo, the section of w at a deep prefix of eta equals c'^kappa(w, eta), where
     kappa(w, eta) = sum of the signs of the c'-letters read while the moving point is 4^oo;
 (4) the character: for random words w, sum over the finitely many eta with kappa != 0 of
     kappa(w, eta) equals the c'-exponent sum of w (the homomorphism e of the theorem), and
     every freely reduced word of length <= 5 trivial at depth 3 has c'-exponent 0.
"""
import random, itertools

D = 11
T = 3                       # the letter 4
def perm_from_cycles(cycles):
    p = list(range(D))
    for cyc in cycles:
        for i, x in enumerate(cyc):
            p[x - 1] = cyc[(i + 1) % len(cyc)] - 1
    return tuple(p)
ALPHA = perm_from_cycles([list(range(1, 12))])
BETA = perm_from_cycles([[1, 2, 3, 4, 8], [5, 10, 7, 11, 6]])
IDP = tuple(range(D))
def pinv(p):
    r = [0] * D
    for x in range(D): r[p[x]] = x
    return tuple(r)

# automaton: state -> (root permutation, {letter: state})
AUT = {'1': (IDP, {}), 'alpha': (ALPHA, {}), 'beta': (BETA, {}),
       'b': (IDP, {0: 'b', 1: 'alpha', 2: 'beta'}),
       'ba': (ALPHA, {0: 'b', 1: 'alpha', 2: 'beta'}),
       'c': (IDP, {T: 'c', T + 1: 'ba'})}

def step(state, x):
    """signed state (name, e) reads letter x: returns (image letter, next signed state)"""
    name, e = state
    p, sec = AUT[name]
    if e == 1:
        return p[x], (sec.get(x, '1'), 1)
    y = pinv(p)[x]
    return y, (sec.get(y, '1'), -1)

def act_word(state, v):
    out = []
    for x in v:
        y, state = step(state, x); out.append(y)
    return tuple(out), state

def strip(t):
    t = list(t)
    while t and t[-1] == T: t.pop()
    return tuple(t)

def act_end(state, t):
    """image of t 4^oo and the stable section (a signed state) along it"""
    img, st = act_word(state, tuple(t) + (T, T))
    assert st[0] in ('1', 'c'), st          # after two extra 4's only c' or 1 is left
    return strip(img), st

def kappa(state, t):
    _, st = act_end(state, t)
    return st[1] if st[0] == 'c' else 0

# ---- depth-n permutation model --------------------------------------------------------
def mul(g, h): return tuple(h[g[v]] for v in range(len(g)))
def inv(g):
    r = [0] * len(g)
    for v, w in enumerate(g): r[w] = v
    return tuple(r)
def ident(n): return tuple(range(D ** n))
def build(root, secs, n):
    m = D ** (n - 1); out = [0] * (D ** n)
    for x in range(D):
        s = secs[x]
        for w in range(m): out[x * m + w] = root[x] * m + s[w]
    return tuple(out)
_cache = {}
def gen(name, n):
    key = (name, n)
    if key in _cache: return _cache[key]
    if n == 0: r = ident(0)
    else:
        p, sec = AUT[name]
        r = build(p, [gen(sec.get(x, '1'), n - 1) for x in range(D)], n)
    _cache[key] = r
    return r
def word(w, n):
    g = ident(n)
    for name, e in w:
        h = gen(name, n); g = mul(g, h if e == 1 else inv(h))
    return g
def power(g, m):
    r = ident(0) if False else tuple(range(len(g)))
    for _ in range(m): r = mul(r, g)
    return r
def section(g, v, n):
    k = len(v); m = D ** (n - k)
    base = sum(x * D ** (k - 1 - i) for i, x in enumerate(v))
    img0 = g[base * m] // m
    return tuple(g[base * m + w] - img0 * m for w in range(m))
def at(g, x, n):
    s = [ident(n - 1)] * D; s = list(s); s[x] = g
    return build(IDP, s, n)

LETTERS = [('alpha', 1), ('alpha', -1), ('beta', 1), ('beta', -1), ('b', 1), ('b', -1), ('c', 1), ('c', -1)]

def main():
    # (1)
    N = 4
    lhs = mul(gen('c', N), inv(at(gen('ba', N - 1), T + 1, N)))
    assert lhs == at(gen('c', N - 1), T, N)
    print("(1) c' ((b alpha)@5)^-1 = c'@4 at depth", N)
    # (2)
    N = 3
    for m in range(1, 13):
        g = power(gen('c', N), m)
        assert section(g, (T,), N) == power(gen('c', N - 1), m)
        assert section(g, (T + 1,), N) == power(gen('ba', N - 1), m)
        assert all(section(g, (x,), N) == ident(N - 1) for x in range(D) if x not in (T, T + 1))
        assert g[:D ** (N - 1)] == ident(N)[:D ** (N - 1)]
    ba = gen('ba', 3); g = ba; nontriv = 0
    for m in range(1, 31):
        if g != ident(3): nontriv += 1
        g = mul(g, ba)
    print("(2) c'^m = (1,1,1,c'^m,(b alpha)^m,1,...) for m = 1..12 at depth 3;"
          f" (b alpha)^m nontrivial at depth 3 for {nontriv} of m = 1..30")
    # (3)
    random.seed(7); ntest = 0
    for trial in range(1500):
        w = [random.choice(LETTERS) for _ in range(random.randint(1, 6))]
        t = strip(tuple(random.randint(0, 10) for _ in range(random.randint(0, 2))))
        K = 0; cur = t; mx = len(cur)
        for l in w:
            K += kappa(l, cur); cur, _ = act_end(l, cur); mx = max(mx, len(cur))
        depth = 2; mlen = mx + 1
        if mlen + depth > 5: continue
        v = tuple(t) + (T,) * (mlen - len(t)); n = mlen + depth
        sec = section(word(w, n), v, n)
        target = word([('c', 1 if K >= 0 else -1)] * abs(K), depth)
        assert sec == target, (w, t, K)
        ntest += 1
    print(f"(3) section at a deep prefix of t 4^oo equals c'^kappa at depth 2 on {ntest} random (word, end) pairs")
    # (4)
    random.seed(11); ntest = 0
    for trial in range(2000):
        w = [random.choice(LETTERS) for _ in range(random.randint(1, 12))]
        # ends where some letter can have kappa != 0: pull 4^oo back along the word
        total = 0
        # enumerate candidate ends: images of () under suffix-inverses
        cands = set()
        for i in range(len(w) + 1):
            cur = ()
            for l in reversed(w[:i]):
                cur, _ = act_end((l[0], -l[1]), cur)
            cands.add(cur)
        for t in cands:
            cur = t
            for l in w:
                total += kappa(l, cur); cur, _ = act_end(l, cur)
        assert total == sum(e for name, e in w if name == 'c'), w
        ntest += 1
    print(f"(4a) sum over ends of kappa(w, eta) = c'-exponent sum on {ntest} random words")
    rel = 0; bad = 0
    gens4 = {l: word([l], 3) for l in LETTERS}
    for L in range(1, 6):
        for w in itertools.product(LETTERS, repeat=L):
            if any(w[i][0] == w[i + 1][0] and w[i][1] == -w[i + 1][1] for i in range(L - 1)): continue
            g = ident(3)
            for l in w: g = mul(g, gens4[l])
            if g == ident(3):
                rel += 1
                if sum(e for name, e in w if name == 'c') != 0: bad += 1
    print(f"(4b) freely reduced words of length <= 5 trivial at depth 3: {rel}; with nonzero c'-exponent: {bad}")
    print("done")

if __name__ == "__main__":
    main()
