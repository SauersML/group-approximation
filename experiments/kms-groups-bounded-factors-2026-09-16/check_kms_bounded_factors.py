#!/usr/bin/env python3
"""Sanity checks for research/artifacts/kms-groups-bounded-factors-2026-09-16.md.

Part A  exact polynomial identities for the 3x3 block of the KMS letters.
Part B  n_0(p): lcm of the multiplicative orders of the roots of chi(x) and chi(x+1).
Part C  explicit finite model: the KMS automorphisms of T_1 (arXiv:1204.6506v5, pp. 23-24),
        restricted to the machine-free semigroup, acting on T_1 / E_n (total a-count >= n).
        Checks relation G2 (letters of different blocks M_i commute), commutation inside H_2,
        that every generator and random words in the generators have order dividing
        p^e * n_0(p) (exponent bound of the predicted image), and that the prime-to-p part
        of the order of each L_2 letter really divides n_0.
Part D  the same checks for a model with one Add command, q_1 = q_2 a_1 (K = 1), where the
        A_0-words are classes of S(M) and nu is the maximal a-count of a representative.
Part E  the BR-conjoint relations G3/G4 on the model matrices of Parts C and D.

Run: timeout 600 python3 check_kms_bounded_factors.py
"""
import os
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")   # single-threaded, as required
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
import itertools
import random
import sympy as sp
import numpy as np

# Matrices are stored as float64 with entries in {0,...,p-1}; every product entry is at most
# dim*(p-1)^2 <= 432*16 < 2^53, so float64 BLAS products followed by reduction mod p are exact.

x = sp.symbols('x')

# ---------------- Part A ----------------
alpha = sp.Matrix([[1, -1, 1], [1, 1, 0], [1, 0, 0]])   # columns: images of e1, e2, e3
E11 = sp.Matrix([[1, 0, 0], [0, 0, 0], [0, 0, 0]])
chi = sp.expand((x * sp.eye(3) - alpha).det())
print("chi_alpha(x) =", chi, "  equals x(x-1)^2+1:", sp.expand(chi - (x * (x - 1) ** 2 + 1)) == 0)
Pexpr = sp.simplify(-1 + x - 1 / x + 1 / (x - 1) - chi / (x * (x - 1)))
print("-1 + x - 1/x + 1/(x-1) == chi(x)/(x(x-1)):", Pexpr == 0)
print("chi(0), chi(1) =", chi.subs(x, 0), chi.subs(x, 1), "(nonzero for every p)")
ai = alpha.inv()
print("alpha^-1 =", ai.tolist(), " E11*alpha^-1*E11 =", (E11 * ai * E11).tolist())
am1 = alpha - sp.eye(3)
print("det(alpha-1) =", am1.det(), " (alpha-1)^-1 =", am1.inv().tolist(),
      " E11*(alpha-1)^-1*E11 =", (E11 * am1.inv() * E11).tolist())
chi_pe = sp.expand((x * sp.eye(3) - (alpha + E11)).det())
print("char poly of alpha+E11 (periodic-shift graded piece, notes only):", chi_pe)

# ---------------- Part B ----------------
def powmod_poly(base, e, f, p):
    result = sp.Poly(1, x, modulus=p)
    b = sp.rem(base, f)
    while e:
        if e & 1:
            result = sp.rem(result * b, f)
        b = sp.rem(b * b, f)
        e >>= 1
    return result

def root_orders_fast(poly, p):
    """lcm over the irreducible factors f of poly mod p of the order of x in GF(p)[x]/(f).
    poly must have nonzero constant term mod p."""
    P = sp.Poly(poly, x, modulus=p)
    _, facs = P.factor_list()
    L = 1
    X = sp.Poly(x, x, modulus=p)
    for f, _mult in facs:
        N = p ** f.degree() - 1
        best = N
        for q, e in sp.factorint(N).items():
            for _ in range(e):
                cand = best // q
                if sp.rem(powmod_poly(X, cand, f, p) - 1, f).is_zero:
                    best = cand
                else:
                    break
        # sanity: x^best == 1 mod f
        assert sp.rem(powmod_poly(X, best, f, p) - 1, f).is_zero
        L = sp.ilcm(L, best)
    return L

n0 = {}
for p in [2, 3, 5, 7, 11, 13]:
    o1 = root_orders_fast(chi, p)
    o2 = root_orders_fast(sp.expand(chi.subs(x, x + 1)), p)
    n0[p] = int(sp.ilcm(o1, o2))
    print(f"p={p}: chi mod p factors {sp.Poly(chi, x, modulus=p).factor_list()[1]}, "
          f"chi(x+1) factors {sp.Poly(sp.expand(chi.subs(x, x+1)), x, modulus=p).factor_list()[1]}, "
          f"n_0={n0[p]} = {sp.factorint(n0[p])}")

# ---------------- Part C ----------------
def build_model(K, n, p):
    """Basis: (ivec in {1,2,3}^K, b in {0,1} (A_0), alph in {0,1}^K (A_j), lvec in N^K with sum < n)."""
    lvecs = [l for l in itertools.product(range(n), repeat=K) if sum(l) < n]
    basis = []
    for iv in itertools.product((1, 2, 3), repeat=K):
        for b in (0, 1):
            for al in itertools.product((0, 1), repeat=K):
                for l in lvecs:
                    basis.append((iv, b, al, l))
    idx = {v: k for k, v in enumerate(basis)}
    dim = len(basis)

    def mat(fn):
        M = np.zeros((dim, dim), dtype=np.int64)
        for k, v in enumerate(basis):
            for (w, c) in fn(v):
                if w in idx:          # terms with total count >= n lie in E_n and are dropped
                    M[idx[w], k] = (M[idx[w], k] + c) % p
        return M.astype(np.float64)

    def block(v, j, shift_ok):
        iv, b, al, l = v
        ij = iv[j]
        def setj(t):
            return tuple(t if s == j else iv[s] for s in range(K))
        if ij == 1:
            out = [((setj(1), b, al, l), 1), ((setj(2), b, al, l), 1), ((setj(3), b, al, l), 1)]
            if shift_ok:
                l2 = tuple(l[s] + (1 if s == j else 0) for s in range(K))
                out.append(((iv, b, al, l2), 1))
            return out
        if ij == 2:
            return [((iv, b, al, l), 1), ((setj(1), b, al, l), -1)]
        return [((setj(1), b, al, l), 1)]

    gens = {}
    for j in range(K):
        def a(v, j=j):
            return [(v, 1)] if v[2][j] == 1 else block(v, j, True)
        def ap(v, j=j):
            return [(v, 1)] if v[2][j] == 1 else [w for w in block(v, j, True)] + [(v, -1)]
        def at(v, j=j):
            if v[1] == 1:
                return [(v, 1)]
            return block(v, j, True)   # u lacks A_0: same shape whether or not u contains A_j
        def atp(v, j=j):
            if v[1] == 1:
                return [(v, 1)]        # reading: identity on words containing A_0 (relation G5c)
            return block(v, j, True) + [(v, -1)]
        def Aj(v, j=j):
            iv, b, al, l = v
            if al[j] == 1:
                return [(v, 1)]
            al2 = tuple(1 if s == j else al[s] for s in range(K))
            return [(v, 1), ((iv, b, al2, l), 1)]
        gens[f"a{j+1}"] = mat(a)
        gens[f"a{j+1}'"] = mat(ap)
        gens[f"~a{j+1}"] = mat(at)
        gens[f"~a{j+1}'"] = mat(atp)
        gens[f"A{j+1}"] = mat(Aj)
    def A0(v):
        iv, b, al, l = v
        return [(v, 1)] if b == 1 else [(v, 1), ((iv, 1, al, l), 1)]
    gens["A0"] = mat(A0)
    return dim, gens

def mm(A, B, p):
    return np.mod(A @ B, p)

def mpow(A, e, p):
    R = np.eye(A.shape[0], dtype=np.float64)
    while e:
        if e & 1:
            R = mm(R, A, p)
        A = mm(A, A, p)
        e >>= 1
    return R

def is_id(A):
    return np.array_equal(A, np.eye(A.shape[0], dtype=np.float64))

def order_brute(A, p, limit):
    B = A.copy()
    for k in range(1, limit + 1):
        if is_id(B):
            return k
        B = mm(B, A, p)
    return None

random.seed(20260916)
allok = True
for (K, n, p) in [(1, 5, 2), (1, 5, 3), (1, 4, 5), (2, 3, 2), (2, 3, 3)]:
    dim, g = build_model(K, n, p)
    names = list(g)
    # G1/G2 checks
    M = {i: [f"a{i}", f"a{i}'", f"A{i}"] for i in range(1, K + 1)}
    M[0] = [f"~a{i}" for i in range(1, K + 1)] + [f"~a{i}'" for i in range(1, K + 1)] + ["A0"]
    g2 = all(np.array_equal(mm(g[u], g[v], p), mm(g[v], g[u], p))
             for i in M for j in M if i < j for u in M[i] for v in M[j])
    L2 = [s for s in names if s[0] in "a~"]
    g1 = all(np.array_equal(mm(g[u], g[v], p), mm(g[v], g[u], p)) for u in L2 for v in L2)
    L1 = [s for s in names if s[0] == "A"]
    g1b = all(np.array_equal(mm(g[u], g[v], p), mm(g[v], g[u], p)) for u in L1 for v in L1) and \
          all(is_id(mpow(g[u], p, p)) for u in L1)
    # orders
    e = 1
    while p ** e < 2 * n + 2:
        e += 1
    N = n0[p] * p ** (e + 1)
    gen_ok = all(is_id(mpow(g[s], N, p)) for s in names)
    # prime-to-p part of L2 letters divides n_0: g^(p^e * n_0) = I already; check prime-to-p exactness
    ords = {}
    if dim <= 130:
        for s in names:
            ords[s] = order_brute(g[s], p, 4000)
    words_ok = True
    for _ in range(25):
        w = np.eye(dim, dtype=np.float64)
        for _k in range(random.randint(2, 9)):
            w = mm(w, g[random.choice(names)], p)
        if not is_id(mpow(w, N, p)):
            words_ok = False
    # image of V = H_1^{H_2}: conjugates of L_1 letters by random H_2 words commute and have order p
    conj = []
    for _ in range(12):
        h = np.eye(dim, dtype=np.float64)
        for _k in range(random.randint(1, 6)):
            h = mm(h, g[random.choice(L2)], p)
        hinv = mpow(h, N - 1, p)          # h^N = I was checked above for random words; recheck for h
        assert is_id(mm(h, hinv, p)), "inverse via h^(N-1) failed"
        conj.append(mm(mm(hinv, g[random.choice(L1)], p), h, p))
    v_ok = all(np.array_equal(mm(c1, c2, p), mm(c2, c1, p)) for c1 in conj for c2 in conj) and \
           all(is_id(mpow(c, p, p)) for c in conj)
    ptp_ok = True
    for s, o in ords.items():
        if o is None:
            ptp_ok = False
            continue
        q = o
        while q % p == 0:
            q //= p
        if n0[p] % q != 0:
            ptp_ok = False
    ok = g2 and g1 and g1b and gen_ok and words_ok and v_ok and ptp_ok
    allok &= ok
    print(f"K={K} n={n} p={p} dim={dim}: G2 {g2}, H2 abelian {g1}, H1 abelian exp p {g1b}, "
          f"generators^{N}=I {gen_ok}, 25 random words^{N}=I {words_ok}, "
          f"12 H2-conjugates of L1 letters commute with order p {v_ok}, "
          f"prime-to-p part of generator orders divides n_0 {ptp_ok if ords else 'n/a (dim>130)'}")
    if ords:
        print("   generator orders:", {s: (o, sp.factorint(o) if o else None) for s, o in ords.items()})
# ---------------- Part D ----------------
# One glass (K=1), states q_1, q_2 (q_0 = 0 unused), one command "1 -> Add(1); 2", i.e. the Minsky
# relation q_1 = q_2 a_1 in S(M).  W_0 classes: {q_1 a^l A^al, q_2 a^(l+1) A^al} and {q_2 A^al}.
# nu(class) = max a-count of a representative; E_n = span of basis vectors with nu >= n.
def build_machine_model(n, p):
    def canon(q, l, al):
        return (1, l - 1, al) if (q == 2 and l >= 1) else (q, l, al)
    def nu0(c):
        q, l, al = c
        return l + 1 if q == 1 else 0
    us = []
    for q in (1, 2):
        for l in range(n):
            for al in (0, 1):
                us.append(("W", q, l, al))
    seen = set()
    for q in (1, 2):
        for l in range(n + 1):
            for al in (0, 1):
                c = canon(q, l, al)
                if nu0(c) < n and c not in seen:
                    seen.add(c)
                    us.append(("W0",) + c)
    def keep(u):
        return u[2] < n if u[0] == "W" else nu0(u[1:]) < n
    def mul_a(u):
        kind, q, l, al = u
        v = (kind, q, l + 1, al) if kind == "W" else ("W0",) + canon(q, l + 1, al)
        return v if keep(v) else None
    def mul_A(u):
        return u[:3] + (1,)
    def ins_A0(u):
        _, q, l, al = u
        v = ("W0",) + canon(q, l, al)
        return v if keep(v) else None
    basis = [(i, u) for i in (1, 2, 3) for u in us]
    idx = {v: k for k, v in enumerate(basis)}
    dim = len(basis)
    def mat(fn):
        M = np.zeros((dim, dim), dtype=np.int64)
        for k, v in enumerate(basis):
            for (w, c) in fn(v):
                if w is not None and w[1] is not None and w in idx:
                    M[idx[w], k] = (M[idx[w], k] + c) % p
        return M.astype(np.float64)
    def block(v):
        i, u = v
        if i == 1:
            return [((1, u), 1), ((2, u), 1), ((3, u), 1), ((1, mul_a(u)), 1)]
        if i == 2:
            return [((2, u), 1), ((1, u), -1)]
        return [((1, u), 1)]
    def a(v):
        return [(v, 1)] if v[1][3] == 1 else block(v)
    def ap(v):
        return [(v, 1)] if v[1][3] == 1 else block(v) + [(v, -1)]
    def at(v):
        return [(v, 1)] if v[1][0] == "W0" else block(v)
    def atp(v):
        return [(v, 1)] if v[1][0] == "W0" else block(v) + [(v, -1)]
    def A1(v):
        i, u = v
        return [(v, 1)] if u[3] == 1 else [(v, 1), ((i, mul_A(u)), 1)]
    def A0(v):
        i, u = v
        return [(v, 1)] if u[0] == "W0" else [(v, 1), ((i, ins_A0(u)), 1)]
    gens = {"a1": mat(a), "a1'": mat(ap), "~a1": mat(at), "~a1'": mat(atp), "A1": mat(A1), "A0": mat(A0)}
    return dim, gens

for (n, p) in [(5, 2), (5, 3)]:
    dim, g = build_machine_model(n, p)
    names = list(g)
    M = {1: ["a1", "a1'", "A1"], 0: ["~a1", "~a1'", "A0"]}
    g2 = all(np.array_equal(mm(g[u], g[v], p), mm(g[v], g[u], p)) for u in M[1] for v in M[0])
    L2 = ["a1", "a1'", "~a1", "~a1'"]
    g1 = all(np.array_equal(mm(g[u], g[v], p), mm(g[v], g[u], p)) for u in L2 for v in L2)
    e = 1
    while p ** e < 2 * n + 2:
        e += 1
    N = n0[p] * p ** (e + 1)
    gen_ok = all(is_id(mpow(g[s], N, p)) for s in names)
    words_ok = True
    for _ in range(25):
        w = np.eye(dim, dtype=np.float64)
        for _k in range(random.randint(2, 9)):
            w = mm(w, g[random.choice(names)], p)
        if not is_id(mpow(w, N, p)):
            words_ok = False
    ptp_ok = True
    ords = {}
    for s in names:
        o = order_brute(g[s], p, 4000)
        ords[s] = o
        if o is None:
            ptp_ok = False
            continue
        q = o
        while q % p == 0:
            q //= p
        if n0[p] % q != 0:
            ptp_ok = False
    L1 = ["A1", "A0"]
    g1b = all(np.array_equal(mm(g[u], g[v], p), mm(g[v], g[u], p)) for u in L1 for v in L1) and \
          all(is_id(mpow(g[u], p, p)) for u in L1)
    conj = []
    for _ in range(12):
        h = np.eye(dim, dtype=np.float64)
        for _k in range(random.randint(1, 6)):
            h = mm(h, g[random.choice(L2)], p)
        hinv = mpow(h, N - 1, p)
        assert is_id(mm(h, hinv, p)), "inverse via h^(N-1) failed"
        conj.append(mm(mm(hinv, g[random.choice(L1)], p), h, p))
    v_ok = all(np.array_equal(mm(c1, c2, p), mm(c2, c1, p)) for c1 in conj for c2 in conj) and \
           all(is_id(mpow(c, p, p)) for c in conj)
    ok = g2 and g1 and g1b and gen_ok and words_ok and v_ok and ptp_ok
    allok &= ok
    print(f"machine q1=q2*a1, K=1 n={n} p={p} dim={dim}: G2 {g2}, "
          f"H2 abelian {g1}, H1 abelian exp p {g1b}, generators^{N}=I (so invertible) {gen_ok}, "
          f"25 random words^{N}=I {words_ok}, 12 H2-conjugates of L1 letters commute with order p {v_ok}, "
          f"prime-to-p part of generator orders divides n_0 {ptp_ok}")
    print("   generator orders:", {s: (o, sp.factorint(o) if o else None) for s, o in ords.items()})

# ---------------- Part E ----------------
# Relations G3/G4 (BR-conjoint relation) on the model matrices.  A matrix M_g has as columns the
# images z^g of the basis vectors, so M_{gh} = M_h M_g (right action, x^g = g^-1 x g).  The group
# relation A^(a^-1) A^-1 = A^((a')^-1) reads  a A a^-1 A^-1 = a' A a'^-1, i.e.
#     M_A^-1 M_a^-1 M_A M_a  ==  M_{a'}^-1 M_A M_{a'}.
# The mirrored identity (left-action convention) is printed as a control; it is not required.
def br_check(g, a, ap, A, p, N):
    Ma, Map, MA = g[a], g[ap], g[A]
    ia, iap, iA = mpow(Ma, N - 1, p), mpow(Map, N - 1, p), mpow(MA, N - 1, p)
    right = np.array_equal(mm(mm(mm(iA, ia, p), MA, p), Ma, p), mm(mm(iap, MA, p), Map, p))
    mirror = np.array_equal(mm(mm(mm(Ma, MA, p), ia, p), iA, p), mm(mm(Map, MA, p), iap, p))
    comm = all(np.array_equal(mm(c, MA, p), mm(MA, c, p))
               for c in (mm(mm(ia, MA, p), Ma, p), mm(mm(Ma, MA, p), ia, p)))
    return right, mirror, comm

def exponent_N(n, p):
    e = 1
    while p ** e < 2 * n + 2:
        e += 1
    return n0[p] * p ** (e + 1)

for (K, n, p) in [(1, 5, 2), (1, 5, 3), (1, 4, 5), (2, 3, 2), (2, 3, 3)]:
    dim, g = build_model(K, n, p)
    N = exponent_N(n, p)
    res = {}
    for j in range(1, K + 1):
        res[f"G3 block {j}"] = br_check(g, f"a{j}", f"a{j}'", f"A{j}", p, N)
        res[f"G4 k={j}"] = br_check(g, f"~a{j}", f"~a{j}'", "A0", p, N)
    ok = all(r[0] and r[2] for r in res.values())
    allok &= ok
    print(f"BR relations K={K} n={n} p={p}: (right-action relation, mirrored control, [A^(a^±1),A]=1) {res} -> {ok}")
for (n, p) in [(5, 2), (5, 3)]:
    dim, g = build_machine_model(n, p)
    N = exponent_N(n, p)
    res = {"G3": br_check(g, "a1", "a1'", "A1", p, N), "G4": br_check(g, "~a1", "~a1'", "A0", p, N)}
    ok = all(r[0] and r[2] for r in res.values())
    allok &= ok
    print(f"BR relations machine q1=q2*a1 n={n} p={p}: {res} -> {ok}")

print("ALL CHECKS PASS" if allok else "SOME CHECK FAILED")
