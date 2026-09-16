#!/usr/bin/env python3
"""Finite-shadow checks for Remark 8.1(b) of
research/artifacts/anti-central-swap-fullness-gives-projective-2026-09-16.md.

The map Phi : F_3[PG] -> S_-, [gbar] -> p' [mu(g,1)] + p'' [mu(1,g)], with
p' = eps_- 2(1 - [d]) and p'' = eps_- 2(1 + [d]), is checked on the finite subgroup
Q = <w, d, h> of G (2x2 scalar matrices in the depth-1 chart), with mu(g_1,g_2) = diag(g_1,g_2)
in the depth-2 chart (4x4 matrices over F_3). Group algebra elements of F_3[G] are dicts keyed by
4x4 matrices; no quotient by +-1 is taken on the target side, since eps_- is explicit.

Checks:
  - p', p'' are orthogonal idempotents with p' + p'' = eps_-;
  - Phi(gbar) is well defined: Phi(g) = Phi(-g) for all g in Q;
  - Phi(g) Phi(h) = Phi(gh) for all g, h in Q, and Phi(1) = eps_-;
  - the Leavitt evaluation (sum of matrices) sends Phi(g) to the identity, so pi o Phi is the
    augmentation;
  - Phi(e_w) is an idempotent below eps_- and different from it.
These are formal consequences of the hand proof; the script only guards against sign slips.

Run: timeout 600 python3 verify_corner_map.py
"""
P = 3


def mmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return tuple(tuple(sum(A[i][r] * B[r][j] for r in range(k)) % P for j in range(m)) for i in range(n))


def mneg(A):
    return tuple(tuple((-x) % P for x in row) for row in A)


def eye(n):
    return tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))


def zero(n):
    return tuple(tuple(0 for _ in range(n)) for _ in range(n))


def block(A, B, C, D):
    return tuple(ra + rb for ra, rb in zip(A, B)) + tuple(rc + rd for rc, rd in zip(C, D))


def diag2(g, h):
    return block(g, zero(len(g)), zero(len(g)), h)


def ga(d):
    return {k: v % P for k, v in d.items() if v % P}


def gadd(x, y, s=1):
    out = dict(x)
    for k, v in y.items():
        out[k] = (out.get(k, 0) + s * v) % P
    return ga(out)


def gscale(x, c):
    return ga({k: c * v for k, v in x.items()})


def gmul(x, y):
    out = {}
    for g, a in x.items():
        for h, b in y.items():
            k = mmul(g, h)
            out[k] = (out.get(k, 0) + a * b) % P
    return ga(out)


def evaluate(x, n=4):
    """Leavitt evaluation in the finite shadow: sum of coefficient times matrix."""
    out = [[0] * n for _ in range(n)]
    for g, a in x.items():
        for i in range(n):
            for j in range(n):
                out[i][j] = (out[i][j] + a * g[i][j]) % P
    return tuple(tuple(r) for r in out)


def closure(gens, one):
    elems, frontier = {one}, [one]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                k = mmul(g, s)
                if k not in elems:
                    elems.add(k)
                    new.append(k)
        frontier = new
    return sorted(elems)


def check(name, cond):
    print(("PASS  " if cond else "FAIL  ") + name)
    if not cond:
        raise SystemExit(1)


I2, Z2 = eye(2), mneg(eye(2))
w1 = ((0, 1), (1, 0))
d1 = ((1, 0), (0, 2))
h1 = ((1, 1), (1, 2))
Q = closure([w1, d1, h1], I2)
print("     |Q| =", len(Q))

I4, Z4 = eye(4), mneg(eye(4))
d2 = diag2(I2, Z2)
ONE = {I4: 1}
eps_m = ga({I4: 2, Z4: -2})
p1 = gmul(eps_m, ga({I4: 2, d2: -2}))
p2 = gmul(eps_m, ga({I4: 2, d2: 2}))
check("p' idempotent", gmul(p1, p1) == p1)
check("p'' idempotent", gmul(p2, p2) == p2)
check("p' p'' = 0", gmul(p1, p2) == {} and gmul(p2, p1) == {})
check("p' + p'' = eps_-", gadd(p1, p2) == eps_m)


def phi(g):
    return gadd(gmul(p1, {diag2(g, I2): 1}), gmul(p2, {diag2(I2, g): 1}))


check("Phi(1) = eps_-", phi(I2) == eps_m)
for g in Q:
    check("Phi well defined on gbar: Phi(g) = Phi(-g)", phi(g) == phi(mneg(g)))
bad = 0
for g in Q:
    for h in Q:
        if gmul(phi(g), phi(h)) != phi(mmul(g, h)):
            bad += 1
check("Phi(g) Phi(h) = Phi(gh) for all %d pairs" % (len(Q) ** 2), bad == 0)
for g in Q:
    check("Leavitt evaluation of Phi(g) is the identity", evaluate(phi(g)) == I4)

e_w_img = gscale(gadd(eps_m, phi(w1)), 2)
check("Phi(e_w) = 2(eps_- + Phi(wbar)) idempotent", gmul(e_w_img, e_w_img) == e_w_img)
check("Phi(e_w) below eps_-", gmul(eps_m, e_w_img) == e_w_img)
check("Phi(e_w) != eps_-", e_w_img != eps_m)
check("evaluation of Phi(e_w) is the identity", evaluate(e_w_img) == I4)
print("ALL CHECKS PASSED")
