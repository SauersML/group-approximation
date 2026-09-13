# Exact two-sided ideal test in T = k<P,Q | P^2=P, Q^2=Q>.
# a = 1 + P(x)(alpha-1), b = 1 + Q(x)(beta-1), alpha=(0 1 2), beta=(0 3 4) on k^5.
# r = entries of [a,b]^3 - 1 ; r' = r with Q -> 1-Q. Is PQ - QP in the ideal generated?
from fractions import Fraction as F
import itertools, sys

def red(w):
    out = []
    for c in w:
        if out and out[-1] == c: continue
        out.append(c)
    return tuple(out)
def tadd(x, y, s=1):
    z = dict(x)
    for w, c in y.items():
        z[w] = z.get(w, 0) + s * c
        if z[w] == 0: del z[w]
    return z
def tmul(x, y):
    z = {}
    for w1, c1 in x.items():
        for w2, c2 in y.items():
            w = red(w1 + w2); z[w] = z.get(w, 0) + c1 * c2
            if z[w] == 0: del z[w]
    return z
ONE = {(): F(1)}; P = {("P",): F(1)}; Q = {("Q",): F(1)}
def scal(c, x): return {w: c * v for w, v in x.items()} if c != 0 else {}

def perm(cycle, n=5):
    M = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    for s in cycle:
        for r in range(n): M[r][s] = F(0)
    for i, s in enumerate(cycle): M[cycle[(i + 1) % len(cycle)]][s] = F(1)
    return M
def inv_perm(M): return [[M[j][i] for j in range(5)] for i in range(5)]
al, be = perm([0, 1, 2]), perm([0, 3, 4])
def tmat(X, S):  # 1 + X (x) (S - I)
    return [[tadd(ONE if i == j else {}, scal(S[i][j] - (1 if i == j else 0), X)) for j in range(5)] for i in range(5)]
def mmul(A, B):
    return [[{} if False else sum_t([tmul(A[i][k], B[k][j]) for k in range(5)]) for j in range(5)] for i in range(5)]
def sum_t(lst):
    z = {}
    for x in lst: z = tadd(z, x)
    return z
def comm(A, Ai, B, Bi): return mmul(mmul(Ai, Bi), mmul(A, B))

def relation_entries(Qx, which):
    A, Ai = tmat(P, al), tmat(P, inv_perm(al))
    B, Bi = tmat(Qx, be), tmat(Qx, inv_perm(be))
    if which == "comm3":
        C = comm(A, Ai, B, Bi); R = mmul(mmul(C, C), C)
    elif which == "ab15":
        AB = mmul(A, B); R = AB
        for _ in range(14): R = mmul(R, AB)
    ents = []
    for i in range(5):
        for j in range(5):
            e = tadd(R[i][j], ONE if i == j else {}, -1)
            if e: ents.append(e)
    return ents

def words(n):
    ws = [()]
    for L in range(1, n + 1):
        for start in ("P", "Q"):
            ws.append(tuple(("P", "Q")[(("P", "Q").index(start) + k) % 2] for k in range(L)))
    return ws

def in_ideal(gens, target, N):
    ws = words(N); vecs = []
    for g in gens:
        for w1 in ws:
            for w2 in ws:
                v = tmul(tmul({w1: F(1)}, g), {w2: F(1)})
                if v: vecs.append(v)
    basis = {}  # pivot word -> reduced vector
    def reduce(v):
        v = dict(v)
        changed = True
        while v:
            piv = max(v, key=lambda w: (len(w), w))
            if piv in basis:
                v = tadd(v, scal(v[piv], basis[piv]), -1)
            else:
                return v, piv
        return v, None
    for v in vecs:
        r, piv = reduce(v)
        if piv is not None:
            c = r[piv]; basis[piv] = scal(1 / c, r)
    r, piv = reduce(target)
    return piv is None, len(basis)


def certificate(gens, target, N):
    ws = words(N); basis = {}  # pivot -> (vector, expression dict)
    def reduce(v, ex):
        v = dict(v); ex = dict(ex)
        while v:
            piv = max(v, key=lambda w: (len(w), w))
            if piv not in basis: return v, ex, piv
            bv, bex = basis[piv]; c = v[piv]
            v = tadd(v, scal(c, bv), -1)
            for k, x in bex.items():
                ex[k] = ex.get(k, 0) - c * x
                if ex[k] == 0: del ex[k]
        return v, ex, None
    for gi, g in enumerate(gens):
        for w1 in ws:
            for w2 in ws:
                v = tmul(tmul({w1: F(1)}, g), {w2: F(1)})
                if not v: continue
                r, ex, piv = reduce(v, {(gi, w1, w2): F(1)})
                if piv is not None:
                    c = r[piv]; basis[piv] = (scal(1 / c, r), {k: x / c for k, x in ex.items()})
    r, ex, piv = reduce(target, {})
    if piv is not None: return None
    return {k: -x for k, x in ex.items()}

def primes(n):
    ps, d = [], 2
    while d * d <= n:
        while n % d == 0:
            ps.append(d); n //= d
        d += 1
    if n > 1: ps.append(n)
    return sorted(set(ps))

QC = tadd(ONE, Q, -1)
target = tadd(tmul(P, Q), tmul(Q, P), -1)
r1 = relation_entries(Q, "comm3"); r2 = relation_entries(QC, "comm3")
gens = r1 + r2
import random
random.seed(5)
order = list(range(len(gens)))
random.shuffle(order)
gens = [gens[i] for i in order]
origin = ["r" if i < len(r1) else "r'" for i in order]
cert = certificate(gens, target, 2)
tot = {}
for (gi, w1, w2), c in cert.items():
    tot = tadd(tot, scal(c, tmul(tmul({w1: F(1)}, gens[gi]), {w2: F(1)})))
print("terms:", len(cert), "verified PQ-QP = sum:", tot == target)
dens = set()
for c in cert.values():
    dens.update(primes(c.denominator))
print("primes in denominators:", sorted(dens))
print("relation sets used:", sorted(set(origin[k[0]] for k in cert)))
print("DONE")

# Usage: /usr/bin/python3.11 idealcert.py  (exact rational arithmetic; seconds)
