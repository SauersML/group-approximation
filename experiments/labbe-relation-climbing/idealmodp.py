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


def modp(x, p):
    z = {}
    for w, c in x.items():
        v = (c.numerator * pow(c.denominator, -1, p)) % p
        if v: z[w] = v
    return z
def in_ideal_p(gens, target, N, p):
    ws = words(N); basis = {}
    def reduce(v):
        v = dict(v)
        while v:
            piv = max(v, key=lambda w: (len(w), w))
            if piv not in basis: return v, piv
            c = v[piv]; bv = basis[piv]
            for w, x in bv.items():
                v[w] = (v.get(w, 0) - c * x) % p
                if v[w] == 0: del v[w]
        return v, None
    for g in gens:
        for w1 in ws:
            for w2 in ws:
                v = modp(tmul(tmul({w1: F(1)}, g), {w2: F(1)}), p)
                if not v: continue
                r, piv = reduce(v)
                if piv is not None:
                    inv = pow(r[piv], -1, p); basis[piv] = {w: (x * inv) % p for w, x in r.items()}
    r, piv = reduce(modp(target, p))
    return piv is None, len(basis)
QC = tadd(ONE, Q, -1)
target = tadd(tmul(P, Q), tmul(Q, P), -1)
r1 = relation_entries(Q, "comm3"); r2 = relation_entries(QC, "comm3")
for p in (2, 3, 5, 7, 53):
    for N in (2, 3, 4):
        print("p =", p, "N =", N, "PQ-QP in ideal:", in_ideal_p(r1 + r2, target, N, p)); sys.stdout.flush()
print("DONE")
