# lx-redpow model test (v2): the exact permutation identities of CharClass/OddPShufflePrimRoot.lean.
# Equiv.Perm convention: (f * g)(i) = f(g(i)).  R = finRotate p: i -> i+1 mod p.  M_r: i -> r*i mod p.
# Module level: P(pi)(t) = t o pi, P(pi) * P(rho) = P(rho * pi), T = P(R); tuples t = distinct symbols.
from math import gcd
def comp(f, g): return lambda i: f(g(i))
def pw(f, k):
    h = lambda i: i
    for _ in range(k):
        h = comp(f, h)
    return h
def P(pi, p): return lambda t: tuple(t[pi(i)] for i in range(p))
def opcomp(A, B): return lambda t: A(B(t))
def oppw(A, k):
    h = lambda t: t
    for _ in range(k):
        h = opcomp(A, h)
    return h
fails = {}
def chk(name, ok):
    fails.setdefault(name, [0, 0]); fails[name][0] += 1
    if not ok: fails[name][1] += 1
for p in [1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13]:
    R = lambda i, p=p: (i + 1) % p
    t0 = tuple(range(p))
    T = P(R, p)
    for r in range(0, 3 * p + 1):
        if gcd(r, p) != 1:
            continue
        M = lambda i, p=p, r=r: (r * i) % p
        s = next((x for x in range(p) if (x * r) % p == 1 % p), None)
        Minv = lambda i, p=p, s=s: (s * i) % p
        chk("bijective", sorted(M(i) for i in range(p)) == list(range(p)))
        for sp in range(0, 2 * p + 1):
            chk("mulPerm_mul_finRotate_pow  M*R^s = R^(rs)*M", all(comp(M, pw(R, sp))(i) == comp(pw(R, r * sp), M)(i) for i in range(p)))
        chk("mulPerm_mul_finRotate  M*R = R^r*M", all(comp(M, R)(i) == comp(pw(R, r), M)(i) for i in range(p)))
        chk("mulPerm_inv_mul_finRotate_pow  Minv*R^r = R*Minv", all(comp(Minv, pw(R, r))(i) == comp(R, Minv)(i) for i in range(p)))
        chk("of_mul_mod_eq_one  M*R^s = R*M", all(comp(M, pw(R, s))(i) == comp(R, M)(i) for i in range(p)))
        chk("mulPerm_inv_eq  Minv*M = id", all(Minv(M(i)) == i for i in range(p)))
        chk("T*P(M) = P(M)*T^r", opcomp(T, P(M, p))(t0) == opcomp(P(M, p), oppw(T, r))(t0))
        chk("T^r*P(Minv) = P(Minv)*T", opcomp(oppw(T, r), P(Minv, p))(t0) == opcomp(P(Minv, p), T)(t0))
        chk("T^s*P(M) = P(M)*T", opcomp(oppw(T, s), P(M, p))(t0) == opcomp(P(M, p), T)(t0))
        if r % p != 1 % p:
            chk("CONTROL (must fail) T^r*P(M) = P(M)*T", opcomp(oppw(T, r), P(M, p))(t0) == opcomp(P(M, p), T)(t0))
        for r2 in range(1, p + 1):
            if gcd(r2, p) != 1: continue
            M2 = lambda i, p=p, r2=r2: (r2 * i) % p
            M12 = lambda i, p=p, r=r, r2=r2: (r * r2 * i) % p
            chk("mulPerm_mul_mulPerm  M_r*M_r2 = M_(r r2)", all(comp(M, M2)(i) == M12(i) for i in range(p)))
for k, (n, f) in fails.items():
    print(f"{k}: checks={n} fails={f}")
