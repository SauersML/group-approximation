"""Sanity checks for alpha-amenably-separable-base-keeps-compression-witness-mf.

F = F_2 = <a,b>, alpha(a)=a^2, alpha(b)=b^2.

1. Integral Magnus map mu: a->1+X, b->1+Y into Z<<X,Y>>/J_n satisfies
   mu(alpha(w)) = tau(mu(w)) with tau(X)=2X+X^2, tau(Y)=2Y+Y^2 (random words).
2. alpha^-1(N_n) = N_n on random words: mu(w)=1 mod J_n iff mu(alpha w)=1.
3. In the mod-2 truncation 2-group G_n = 1+(X,Y)/I_n, the subgroup generated
   by images of a^(2^m), b^(2^m) omits the images of chosen gamma not in
   alpha^m(F): separation of alpha^m(F) through an amenable alpha-compatible
   quotient (here a finite 2-group, which contains some N_n).
"""
import random
from itertools import product

N = 5  # truncation degree: keep monomials of degree < N


def mul(p, q, mod=None):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            if len(m1) + len(m2) >= N:
                continue
            m = m1 + m2
            r[m] = r.get(m, 0) + c1 * c2
    if mod:
        r = {m: c % mod for m, c in r.items()}
    return {m: c for m, c in r.items() if c}


ONE = {(): 1}


def gen(letter, inv, mod=None):
    v = 'X' if letter == 'a' else 'Y'
    if not inv:
        return {(): 1, (v,): 1}
    # (1+v)^-1 = sum (-v)^i
    p = {tuple([v] * i): (-1) ** i for i in range(N)}
    if mod:
        p = {m: c % mod for m, c in p.items() if c % mod}
    return p


def mu(word, mod=None):
    p = dict(ONE)
    for (l, inv) in word:
        p = mul(p, gen(l, inv, mod), mod)
    return p


def alpha(word):
    return [x for x in word for _ in range(2)]


def tau(p):
    # substitute X -> 2X+X^2, Y -> 2Y+Y^2
    r = {}
    for m, c in p.items():
        t = dict(ONE)
        for v in m:
            t = mul(t, {(v,): 2, (v, v): 1})
        for mm, cc in t.items():
            r[mm] = r.get(mm, 0) + c * cc
    return {m: c for m, c in r.items() if c}


def rand_word(L):
    w = []
    while len(w) < L:
        x = (random.choice('ab'), random.random() < 0.5)
        if w and w[-1][0] == x[0] and w[-1][1] != x[1]:
            continue
        w.append(x)
    return w


random.seed(1)
for _ in range(200):
    w = rand_word(random.randint(1, 8))
    assert mu(alpha(w)) == tau(mu(w)), w
    assert (mu(w) == ONE) == (mu(alpha(w)) == ONE)
# commutators lie deep; check a word in N_n: [[a,b],[a,b]]-type trivial, use
# long commutator [a,[a,[a,[a,b]]]] of weight 5 >= N lies in N_5
def comm(u, v):
    inv = lambda w: [(l, not i) for (l, i) in reversed(w)]
    return u + v + inv(u) + inv(v)
A, B = [('a', False)], [('b', False)]
c5 = comm(A, comm(A, comm(A, comm(A, B))))
assert mu(c5) == ONE and mu(alpha(c5)) == ONE
print("checks 1-2 passed (tau-intertwining, alpha^-1(N_5)=N_5 on samples)")


def key(p):
    return tuple(sorted(p.items()))


def subgroup(gens):
    seen = {key(ONE): ONE}
    frontier = [ONE]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = mul(p, g, 2)
                k = key(q)
                if k not in seen:
                    seen[k] = q
                    nxt.append(q)
        frontier = nxt
    return seen


for m in (1, 2):
    e = 2 ** m
    H = subgroup([mu(A * e, 2), mu(B * e, 2)])
    tests = {
        'a': A,
        'b a b^-1': B + A + [('b', True)],
        '[a,b]': comm(A, B),
        'a^(2^(m-1))': A * (e // 2),
        'b a^2 b^-1 a^2': B + A * 2 + [('b', True)] + A * 2,
    }
    ins = {'a^(2^m) b^(2^m)': A * e + B * e}
    for name, w in tests.items():
        assert key(mu(w, 2)) not in H, (m, name)
    for name, w in ins.items():
        assert key(mu(w, 2)) in H, (m, name)
    print(f"m={m}: |<a^{e},b^{e}> image| = {len(H)}; tested gammas separated")
print("all checks passed")
