# Model test for psi_W : W -> W (x) W over F_p[Z/p], p = 3, 5, 7.
# Components in bidegree (a,b) live in R = F_p[Z/p x Z/p]; elements are dicts (x,y) -> coeff mod p.
import itertools, sys
def mul(r, s, p):
    out = {}
    for (x1, y1), c1 in r.items():
        for (x2, y2), c2 in s.items():
            k = ((x1 + x2) % p, (y1 + y2) % p)
            out[k] = (out.get(k, 0) + c1 * c2) % p
    return {k: v for k, v in out.items() if v}
def add(r, s, p, sc=1):
    out = dict(r)
    for k, v in s.items():
        out[k] = (out.get(k, 0) + sc * v) % p
    return {k: v for k, v in out.items() if v}
def mono(x, y): return {(x, y): 1}
def one(): return mono(0, 0)
def T1(p): return mono(1 % p, 0)
def T2(p): return mono(0, 1 % p)
def D(p): return mono(1 % p, 1 % p)
def s_of(t, p): return add(t, one(), p, -1)
def N_of(t, p):
    out, cur = {}, one()
    for _ in range(p):
        out = add(out, cur, p); cur = mul(cur, t, p)
    return out
def c(k, t, p): return s_of(t, p) if k % 2 == 0 else N_of(t, p)
def phi(a, b, p):
    if a % 2 == 0: return one()
    if b % 2 == 0: return T2(p)
    return {(u, v): 1 for u in range(p) for v in range(p) if u < v}
def check(p, nmax):
    bad = 0
    for n in range(nmax + 1):
        for a in range(n + 1):
            b = n - a
            lhs = add(mul(c(a, T1(p), p), phi(a + 1, b, p), p),
                      mul(c(b, T2(p), p), phi(a, b + 1, p), p), p, (-1) ** a)
            rhs = mul(c(n, D(p), p), phi(a, b, p), p)
            if lhs != rhs: bad += 1; print("FAIL chain", p, a, b)
    # counits: (eps x 1) keeps a = 0 and pushes forward along snd; (1 x eps) keeps b = 0 along fst
    for n in range(nmax + 1):
        l = phi(0, n, p); r = phi(n, 0, p)
        fl = {}; fr = {}
        for (x, y), v in l.items(): fl[y] = (fl.get(y, 0) + v) % p
        for (x, y), v in r.items(): fr[x] = (fr.get(x, 0) + v) % p
        if {k: v for k, v in fl.items() if v} != {0: 1} or {k: v for k, v in fr.items() if v} != {0: 1}:
            bad += 1; print("FAIL counit", p, n)
    red = [sum(phi(a, b, p).values()) % p for (a, b) in [(0, 0), (1, 0), (1, 1)]]
    print("p", p, "n<=", nmax, "failures", bad, "reduced (even,odd-even,odd-odd)", red)
for p in (3, 5, 7):
    check(p, 2 * (p - 1) + 3)
