#!/usr/bin/env python3
"""Two-sided b/d ladder in Higman's group H4 = G_b *_F G_d, F = <a,c> free.

Conventions: x^y = y^-1 x y, [x,y] = x^-1 y^-1 x y.  Words in the free group F on a, c are
lists of ints: 1 = a, -1 = a^-1, 2 = c, -2 = c^-1.

Relations used (all hold in H4, and in its quotients):
  b^-1 c_j b = c_j^(N_j),  c_j = a^j c a^-j,  j >= 0,   N_j = 2^(P^j)
  d^-1 a_i d = a_i^(N_i),  a_i = c^i a c^-i,  i >= 0,
with P = 2 for the pair (a, c).  For the pair (alpha, gamma) = (a^m, c^m) the same formulas hold
with alpha, gamma in place of a, c and P = 2^m.  So every computation below is run for P = 2, 4, 8
(m = 1, 2, 3) and for P symbolic (heights kept as formal pairs, valid for all large P).

iota_b(w): for w in P_>=0 = <c_j : j >= 0>, the word of b^-1 w b (replace each c^e at a-height j by
c^(e N_j)).  iota_d is the mirror image.

Chain (k = 3):  w0 in F''' ∩ P_>=0;  u1 = b^-1 w0 b = iota_b(w0);  v1 = c^n u1 c^-n;  u2 = d^-1 v1 d;
v2 = a^n' u2 a^-n';  u3 = b^-1 v2 b.  All lie in ncl_H4(F''') ∩ F.

Key quantity.  For u in F with c-exponent 0, let
  S(u) = sum over c-letters l of u of  eps_l * t^kappa(l)   in Z[t_h : h in Z],
where kappa(l)_h is the net exponent of the a-letters of u before l that sit at c-height h.
Then E(u2) := image of u2 in P/P' = Z[X^+-1] equals S(v1) evaluated at t_h -> X^(N_h), and for
n large this is nonzero iff S(u1) is nonzero as a formal sum (super-exponential separation of
the N_h).  E(u2) != 0 gives, for n' large, c-exponent(u3) = sum_j N_(j+n') E_j(u2) != 0.

For the calibration k = 2 the chain is one step shorter: w0 in F'' ∩ P_>=0, u1 = iota_b(w0),
and the image of u1 in P_d/P_d' = Z[Y^+-1] (sum over a-letters of eps * Y^height) must be nonzero.
"""
from collections import Counter
import itertools, sys

A, a_, C, c_ = 1, -1, 2, -2


def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def inv(w):
    return [-x for x in reversed(w)]


def mul(*ws):
    r = []
    for w in ws:
        r = red(r + list(w))
    return r


def comm(x, y):
    return mul(inv(x), inv(y), x, y)


def cj(j, e=1):
    """c_j^e = a^j c^e a^-j."""
    s = [A] * j if j >= 0 else [a_] * (-j)
    return mul(s, [C] * e if e > 0 else [c_] * (-e), inv(s))


def exps(w):
    ea = sum(1 if x == A else -1 for x in w if abs(x) == 1)
    ec = sum(1 if x == C else -1 for x in w if abs(x) == 2)
    return ea, ec


def iota_b(w, P):
    """Word of b^-1 w b for w in P_>=0 (numeric P)."""
    out, h = [], 0
    for x in w:
        if abs(x) == 1:
            h += 1 if x == A else -1
            out.append(x)
        else:
            if h < 0:
                raise ValueError("c-letter at negative a-height")
            out.extend([x] * (2 ** (P ** h)))
    return red(out)


def S_numeric(u):
    """Formal sum S(u) for a word u with c-exponent 0."""
    kappa = Counter()
    h = 0
    S = Counter()
    for x in u:
        if abs(x) == 1:
            kappa[h] += 1 if x == A else -1
            if kappa[h] == 0:
                del kappa[h]
        else:
            e = 1 if x == C else -1
            S[frozenset(kappa.items())] += e
            h += e
    return Counter({k: v for k, v in S.items() if v != 0})


def S_symbolic(w0):
    """Formal S(iota_b(w0)) for w0 using only c_0, c_1, with N_0 = 2 and N_1 = M formal.

    Heights (c-heights of the a-letters in iota_b(w0)) are 2p + qM, stored as (p, q), where p, q
    are the net numbers of c-letters of w0 at a-height 0, 1 seen so far.  A block c^(e N_j)
    contributes e N_j t^kappa, since kappa is constant along a block.  The coefficient of t^kappa is
    stored as (c0, c1), meaning 2 c0 + M c1.
    """
    kappa = Counter()
    p = q = 0
    ah = 0
    S = {}
    for x in w0:
        if abs(x) == 1:
            kappa[(p, q)] += 1 if x == A else -1
            if kappa[(p, q)] == 0:
                del kappa[(p, q)]
            ah += 1 if x == A else -1
        else:
            e = 1 if x == C else -1
            assert ah in (0, 1)
            key = frozenset(kappa.items())
            c0, c1 = S.get(key, (0, 0))
            S[key] = (c0 + e, c1) if ah == 0 else (c0, c1 + e)
            if ah == 0:
                p += e
            else:
                q += e
    S = {k: v for k, v in S.items() if v != (0, 0)}
    ps = [pq[0] for k in S for (pq, _) in k] + [0]
    prange = max(ps) - min(ps)
    return S, prange


def valid_bound(S, prange):
    """Smallest M0 such that for every M > M0 the formal sum specializes to a nonzero sum.

    (i) (p, q) -> 2p + qM is injective on the occurring heights once M > 2 prange, so distinct
    formal keys stay distinct; (ii) some key has coefficient 2 c0 + M c1 != 0 for M > M0.
    """
    best = None
    for k, (c0, c1) in S.items():
        if c1 == 0:
            b = 0
        else:
            b = abs(2 * c0) // abs(c1) + 1
        best = b if best is None else min(best, b)
    return max(2 * prange, best)


def Ed_numeric(u):
    """Image of u (c-exponent 0) in P_d/P_d' = Z[Y^+-1]: a-letters weighted Y^height."""
    E, h = Counter(), 0
    for x in u:
        if abs(x) == 1:
            E[h] += 1 if x == A else -1
        else:
            h += 1 if x == C else -1
    return Counter({k: v for k, v in E.items() if v})


def in_P_ge0(w):
    h = 0
    for x in w:
        if abs(x) == 1:
            h += 1 if x == A else -1
        elif h < 0:
            return False
    return h == 0


def E_u2_exact(u1, P):
    """Exact image of u2 = d^-1 (c^n u1 c^-n) d in P/P' = Z[X^+-1], n = -(min c-height of a-letter).

    Returns (n, poly) with poly a dict exponent -> coefficient (exponents are big integers)."""
    h, hs = 0, []
    for x in u1:
        if abs(x) == 1:
            hs.append(h)
        else:
            h += 1 if x == C else -1
    n = -min(hs)
    Nh = {}
    def N(t):
        if t not in Nh:
            Nh[t] = 2 ** (P ** t)
        return Nh[t]
    poly = Counter()
    ah = 0       # a-exponent of the prefix of u2
    h = n
    for x in u1:
        if abs(x) == 1:
            ah += N(h) if x == A else -N(h)
        else:
            e = 1 if x == C else -1
            poly[ah] += e
            h += e
    # the conjugating letters c^n, c^-n contribute +n X^0 and -n X^(total) with total = 0
    assert ah == 0
    return n, Counter({k: v for k, v in poly.items() if v})


def brute_force_check():
    """Cross-check E(d^-1 v d) = S(v)|_(t_h -> X^(N_h)) on small v, by expanding d^-1 v d."""
    import random
    rnd = random.Random(1)
    P = 2
    checked = 0
    def rword():
        # random word in a_0, a_1, a_2 (heights <= 2, so N <= 16)
        r = []
        for _ in range(rnd.randint(1, 5)):
            i = rnd.randint(0, 2)
            e = rnd.choice((1, -1))
            r = mul(r, [C] * i, [A] if e > 0 else [a_], [c_] * i)
        return r
    for trial in range(300):
        # v = [r1, r2] lies in P_d' and in (P_d)_>=0, so d^-1 v d = iota_d(v) lies in F' <= P
        v = comm(rword(), rword())
        # expand iota_d
        u, h = [], 0
        for x in v:
            if abs(x) == 1:
                u.extend([x] * (2 ** (P ** h)))
            else:
                u.append(x)
                h += 1 if x == C else -1
        u = red(u)
        # image of u in P/P' only makes sense if u in P (a-exponent 0); compute c-letter counts
        # by a-height directly
        if exps(u)[0] != 0:
            continue
        direct, ah = Counter(), 0
        for x in u:
            if abs(x) == 1:
                ah += 1 if x == A else -1
            else:
                direct[ah] += 1 if x == C else -1
        direct = Counter({k: w for k, w in direct.items() if w})
        S = S_numeric(v)
        ev = Counter()
        for key, coef in S.items():
            ev[sum(cnt * 2 ** (P ** hh) for hh, cnt in key)] += coef
        ev = Counter({k: w for k, w in ev.items() if w})
        assert ev == direct, (v, ev, direct)
        checked += 1
    return checked


def main():
    x = mul(cj(1), cj(0, -1))          # c_1 c_0^-1  in F'
    y = mul(cj(0, -1), cj(1))          # c_0^-1 c_1  in F'
    x2 = mul(cj(0), cj(1), cj(0, -2))  # c_0 c_1 c_0^-2 in F'
    y2 = mul(cj(1, -1), cj(0), cj(1, -1), cj(0))  # in F'
    f2a = comm(x, y)
    f2b = comm(x2, y2)
    f2c = comm(y, x2)
    print("brute-force check of E(d^-1 v d) = S(v)(X^N_h):", brute_force_check(), "random words agree")
    print("== calibration k = 2 (known theorem: metabelian <a^m,c^m> collapses) ==")
    for name, w0 in [("[x,y]", f2a), ("[x2,y2]", f2b)]:
        assert in_P_ge0(w0) and exps(w0) == (0, 0)
        for P in (2, 4, 8):
            u1 = iota_b(w0, P)
            E = Ed_numeric(u1)
            print(f"  w0={name} P={P}: |u1|={len(u1)}, exps(u1)={exps(u1)}, "
                  f"image of u1 in P_d/P_d' nonzero: {bool(E)}  {dict(sorted(E.items()))}")
    print("== k = 3 chain ==")
    w0 = comm(f2a, f2c)
    print("  w0 = [[x,y],[y,x2]], x = c_1 c_0^-1, y = c_0^-1 c_1, x2 = c_0 c_1 c_0^-2")
    print("  w0 as a word (1=a, -1=a^-1, 2=c, -2=c^-1):", w0)
    assert in_P_ge0(w0) and exps(w0) == (0, 0)
    for P in (2, 4, 8, 16):
        u1 = iota_b(w0, P)
        assert exps(u1) == (0, 0)
        S = S_numeric(u1)
        line = (f"  P={P} (m={P.bit_length()-1}): |u1|={len(u1)}, S(u1) nonzero: {bool(S)}"
                f" ({len(S)} monomials, l1 = {sum(abs(v) for v in S.values())})")
        if P == 2:
            n, poly = E_u2_exact(u1, P)
            line += (f"\n    exact E(u2) with n={n}: {len(poly)} nonzero terms, l1 = "
                     f"{sum(abs(v) for v in poly.values())}, max exponent has "
                     f"{max(abs(k) for k in poly).bit_length()} bits")
        print(line)
    S, prange = S_symbolic(w0)
    M0 = valid_bound(S, prange)
    print(f"  symbolic (N_0 = 2, N_1 = M = 2^P formal): {len(S)} nonzero formal terms, "
          f"p-range {prange}; nonzero for every M > {M0}")
    print(f"  M = 2^(2^m) > {M0} for m >= {next(m for m in range(1, 10) if 2 ** (2 ** m) > M0)};"
          f" smaller m checked numerically above")
    for name, w in [("[[x,y],[x2,y2]]", comm(f2a, f2b)), ("[[x2,y2],[y,x2]]", comm(f2b, f2c))]:
        S2 = S_numeric(iota_b(w, 2))
        print(f"  other w0 = {name}: S(u1) nonzero at P=2: {bool(S2)}")


if __name__ == "__main__":
    main()
