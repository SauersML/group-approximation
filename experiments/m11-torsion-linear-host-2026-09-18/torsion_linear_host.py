#!/usr/bin/env python3
"""Exact word problem and exponent checks for R' = <M_11, a, b, c> on the 11-ary tree, where
the linear generator's second section is the balanced element g = a@1 (a@2)^{-1}.

Conventions (as in m11-linear-activity-self-replicating-group): right actions,
(x w)^g = x^{pi_g} w^{g|_x},  (gh)|_x = g|_x h|_{x^{pi_g}}.  Letters 0..10 stand for 1..11.
  a = (a, 1, ..., 1) alpha         alpha = (1,2,...,11)
  b = (b, alpha, beta, 1, ...)     beta  = (1,2,3,4,8)(5,10,7,11,6)
  c = (c, g, 1, ..., 1)            (the new linear generator)
  g = (a, a^-1, 1, ..., 1)         (= a alpha^-1 a^-1 alpha, checked below)
Every letter section is one letter or empty, so reduced sections never get longer and the
section closure of a word is finite: a word is trivial iff every word in its closure has
trivial root permutation.  Also computes the section-exponent screen of the claim.
"""
import itertools, sys
import sympy

D = 11
ID = tuple(range(D))
def perm_from_cycles(cycles):
    p = list(range(D))
    for cyc in cycles:
        for i, x in enumerate(cyc):
            p[x - 1] = cyc[(i + 1) % len(cyc)] - 1
    return tuple(p)
def mul(p, q):          # right action: x^(pq) = (x^p)^q
    return tuple(q[p[x]] for x in range(D))
def inv(p):
    r = [0] * D
    for x in range(D): r[p[x]] = x
    return tuple(r)

ALPHA = perm_from_cycles([list(range(1, 12))])
BETA = perm_from_cycles([[1, 2, 3, 4, 8], [5, 10, 7, 11, 6]])
M11_GENS = [ALPHA, tuple(x - 1 for x in [1, 2, 7, 10, 6, 4, 11, 3, 9, 5, 8])]  # GAP: Stab_{M12}(12)

def closure(gens):
    seen = {ID}; frontier = [ID]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = mul(g, s)
                if h not in seen: seen.add(h); nxt.append(h)
        frontier = nxt
    return seen
M11 = closure(M11_GENS)
assert len(M11) == 7920 and BETA in M11

ROOT = {'a': ALPHA, 'b': ID, 'c': ID, 'g': ID}
SEC = {'a': {0: ('a', 1)},
       'b': {0: ('b', 1), 1: ('p', ALPHA), 2: ('p', BETA)},
       'c': {0: ('c', 1), 1: ('g', 1)},
       'g': {0: ('a', 1), 1: ('a', -1)}}

def letter_root(l):
    if l[0] == 'p': return l[1]
    r = ROOT[l[0]]
    return r if l[1] == 1 else inv(r)
def letter_section(l, y):
    if l[0] == 'p': return None
    s, e = l
    if e == 1:
        return SEC[s].get(y)
    y0 = inv(ROOT[s])[y]
    t = SEC[s].get(y0)
    if t is None: return None
    return ('p', inv(t[1])) if t[0] == 'p' else (t[0], -t[1])
def raw_section(w, x):
    out = []; y = x
    for l in w:
        t = letter_section(l, y)
        if t is not None: out.append(t)
        y = letter_root(l)[y]
    return tuple(out)
def root(w):
    p = ID
    for l in w: p = mul(p, letter_root(l))
    return p
def reduce(w):
    out = []
    for l in w:
        if l[0] == 'p':
            if out and out[-1][0] == 'p':
                q = mul(out[-1][1], l[1]); out.pop()
                if q != ID: out.append(('p', q))
            elif l[1] != ID: out.append(l)
        elif out and out[-1][0] == l[0] and out[-1][1] == -l[1]:
            out.pop()
        else:
            out.append(l)
    return tuple(out)
def is_trivial(w, limit=400000):
    start = reduce(w); seen = {start}; stack = [start]
    while stack:
        u = stack.pop()
        if root(u) != ID: return False
        for x in range(D):
            v = reduce(raw_section(u, x))
            if v not in seen:
                seen.add(v); stack.append(v)
                if len(seen) > limit: raise RuntimeError("closure too large")
    return True
def ex(w, s): return sum(l[1] for l in w if l[0] == s)
def nf(w): return sum(1 for l in w if l[0] != 'p')

A, Ai, B, Bi, C, Ci, G, Gi = ('a', 1), ('a', -1), ('b', 1), ('b', -1), ('c', 1), ('c', -1), ('g', 1), ('g', -1)
Pa, Pai, Pb, Pbi = ('p', ALPHA), ('p', inv(ALPHA)), ('p', BETA), ('p', inv(BETA))
def winv(w): return tuple((('p', inv(l[1])) if l[0] == 'p' else (l[0], -l[1])) for l in reversed(w))
def conj(w, p): return (('p', inv(p)),) + w + (('p', p),)
def power(w, n): return w * n if n >= 0 else winv(w) * (-n)

def screen(name, letters, rows):
    """rows[s] = exponent vector of sum_x s|_x over the letters; returns char poly data."""
    t = sympy.symbols('t')
    Mx = sympy.Matrix([[rows[s].get(u, 0) for u in letters] for s in letters])
    chi = sympy.factor_list(Mx.charpoly(t).as_expr())
    bound = 0; facs = []
    for f, m in chi[1]:
        pf = sympy.Poly(f, t)
        c0 = pf.eval(0)
        facs.append(f"({f})^{m}")
        if abs(c0) == 1: bound += pf.degree() * m
    print(f"(5) screen {name}: chi = {' '.join(facs)}; b_1 <= {bound}")
    return bound

def main():
    print("M_11 order", len(M11), "; alpha, beta in M_11: True")
    a_at1 = (A, Pai)                     # a@1 = a alpha^-1
    a_at2 = conj(a_at1, ALPHA)           # a@2 = alpha^-1 (a@1) alpha
    g_word = a_at1 + winv(a_at2)         # a@1 (a@2)^-1
    U = ()
    for k in range(11):
        U += power((B,), -k) + (C,) + power((B,), k)
    checks = {
        "g = a@1 (a@2)^-1": (winv((G,)) + g_word, True),
        "g = a alpha^-1 a^-1 alpha": (winv((G,)) + (A, Pai, Ai, Pa), True),
        "[a@1, a@2] = 1": (winv(a_at1) + winv(a_at2) + a_at1 + a_at2, True),
        "U = prod_k b^-k c b^k = 1  (e_c(U) = 11)": (U, True),
        "b^55 = 1": ((B,) * 55, True),
        "b^11 = 1": ((B,) * 11, False),
        "c^11 = 1": ((C,) * 11, False),
        "c^121 = 1": ((C,) * 121, False),
        "g^11 = 1": ((G,) * 11, False),
        "a^11 = 1": ((A,) * 11, False),
        "[b, c] = 1": ((Bi, Ci, B, C), False),
    }
    for name, (w, expect) in checks.items():
        got = is_trivial(w)
        print(f"(1) {name}: {got}  (expected {expect})"); assert got == expect
    print(f"    e_c(U) = {ex(U, 'c')}, e_a(U) = {ex(U, 'a')}, |U| = {len(U)}")
    # calibration: with the old linear generator c = (c, a, 1, ...) the same word is NOT trivial
    SEC['c'] = {0: ('c', 1), 1: ('a', 1)}
    old = is_trivial(U)
    print(f"(1') calibration, old c = (c, a, 1, ...): U = 1 is {old}  (expected False)"); assert not old
    SEC['c'] = {0: ('c', 1), 1: ('g', 1)}
    # (2) mass identities on all words of length <= 5 over {a,b,c,g,alpha,beta}^+-1
    alph = [A, Ai, B, Bi, C, Ci, G, Gi, Pa, Pai, Pb, Pbi]
    cnt = 0
    for L in range(1, 6):
        for w in itertools.product(alph, repeat=L):
            secs = [raw_section(w, x) for x in range(D)]
            assert sum(ex(s, 'a') for s in secs) == ex(w, 'a')
            assert sum(ex(s, 'c') for s in secs) == ex(w, 'c')
            assert sum(ex(s, 'g') for s in secs) == ex(w, 'c')
            assert all(len(s) <= nf(w) for s in secs)
            cnt += 1
    print(f"(2) e_a and e_c mass identities, e_g mass = e_c, and length bound hold on all {cnt} words of length <= 5")
    # (3) stable-word bound |e_a| <= 1 over {a,b,c,g}^+-1
    nfal = [A, Ai, B, Bi, C, Ci, G, Gi]; worst = 0; nstable = 0
    for L in range(1, 7):
        for w in itertools.product(nfal, repeat=L):
            for x in range(D):
                s = raw_section(w, x)
                if len(s) == L and nf(s) == L:
                    nstable += 1; worst = max(worst, abs(ex(w, 'a')))
    print(f"(3) {nstable} stable (word, point) pairs up to length 6; max |e_a| = {worst}"); assert worst <= 1
    # (4) relation census: reduced words of length <= 5 over {a,b,c,alpha,beta}^+-1 trivial in R'
    alph2 = [A, Ai, B, Bi, C, Ci, Pa, Pai, Pb, Pbi]
    rel = 0; bad = 0
    for L in range(1, 6):
        for w in itertools.product(alph2, repeat=L):
            if reduce(w) != w or root(w) != ID: continue
            if is_trivial(w):
                rel += 1
                if ex(w, 'a') != 0: bad += 1; print("   relation with e_a != 0:", w)
    print(f"(4) trivial reduced words of length <= 5: {rel}; with e_a != 0: {bad}"); assert bad == 0
    # (5) the unimodular screen
    screen("old R = <M11,a,b,c>, c=(c,a)", ['a', 'b', 'c'], {'a': {'a': 1}, 'b': {'b': 1}, 'c': {'c': 1, 'a': 1}})
    screen("new R' , c=(c,g), g=(a,a^-1)", ['a', 'b', 'c', 'g'], {'a': {'a': 1}, 'b': {'b': 1}, 'c': {'c': 1, 'g': 1}, 'g': {}})
    screen("design z=(z,h), h=(z,z,1..)alpha", ['z', 'h'], {'z': {'z': 1, 'h': 1}, 'h': {'z': 2}})
    screen("design z=(z,h), h=(z,z,z,1..)alpha", ['z', 'h'], {'z': {'z': 1, 'h': 1}, 'h': {'z': 3}})
    print("done")

if __name__ == "__main__":
    main()
