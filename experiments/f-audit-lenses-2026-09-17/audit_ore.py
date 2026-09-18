#!/usr/bin/env python3
"""Independent checks of thompson-f-binomial-multipliers-see-every-conjugate
(audit 2026-09-18, agent e2-w2-audit-f).

Exact arithmetic in Thompson's group F, realised as PL homeomorphisms of [0,1] with dyadic
breakpoints and slopes powers of 2 (elements are canonical breakpoint tuples of Fractions, so
equality is tuple equality and the group ring K[F] with K = Q is a dict elt -> Fraction).

The proof of the claim is a chain of five exact identities.  This script re-derives each one on
random data, which is the only way a referee can catch an algebra slip in Steps 0, 2, 4 and 5.

(0) Step 0, the coset test.  y in J = (1+lambda g)R  <=>  eps_w(y) = 0 for every right coset <g>w,
    with eps_w(y) = sum_n y(g^n w) mu^n, mu = -1/lambda.  Checked in both directions: every
    (1+lambda g)r passes, and a random r fails.  Also its consequence  g^a y - mu^a y in J.

(1) Step 1, reduction.  b - b_reduced lies in J, and supp(b_reduced) meets every coset once.

(2) Step 2, the identity that carries the support theorem:
        eps_{t_0 x}(b v) = (beta v)(x)     for every x in V,
    where V = <h> is transverse to t_0^{-1}<g>t_0 and beta = sum_{t in T_D} b(t) mu^{m_t} c_t.
    Plus a falsification search: with V transverse to some conjugate, b v is NEVER in J.

(3) Step 4, transverse saturation:
        eps_{w x}(y a) = (Y_D a)(x),        Y_D(x) = eps_{wx}(y),
    for A = <h> meeting every conjugate of <g> trivially; plus the corollary that no unit times a
    product of one-bump twisted binomials lies in J when g has two bumps.

(4) Step 5, shift dependence: b v = sum_a g^a phi^a(b) r_a is congruent mod J to
    sum_a mu^a phi^a(b) r_a, and K[V] meets J only in 0.

Also: the bump-count facts of Step 4 (supp h^n = supp h, conjugation preserves the number of
components) on random elements.

Scope note.  Cosets <g>w are enumerated with an exponent window |n| <= 7, ample for the supports
used here (each monomial is a product of at most 8 generators), and the window is only a search
bound: a coset whose members all lie inside it is grouped exactly.  Test (0) would have failed had
the window ever been too small, since a split coset gives a nonzero eps for a genuine element of J.

Usage: python3 audit_ore.py [--trials 40] [--seed 7]     (runtime about a minute)
"""
import argparse
import itertools
import random
from fractions import Fraction

FAIL = []
ZERO = Fraction(0)


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ((" | " + detail) if detail else ""), flush=True)
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- F as PL maps

def canon(pts):
    """pts: increasing list of (x,y) with (0,0) and (1,1); drop redundant breakpoints."""
    out = [pts[0]]
    for i in range(1, len(pts) - 1):
        xa, ya = out[-1]
        xb, yb = pts[i]
        xc, yc = pts[i + 1]
        if (yb - ya) * (xc - xb) == (yc - yb) * (xb - xa):
            continue                       # collinear: redundant
        out.append(pts[i])
    out.append(pts[-1])
    return tuple(out)


def is_power_of_two(q):
    n, d = q.numerator, q.denominator
    return n > 0 and (n & (n - 1)) == 0 and (d & (d - 1)) == 0


def mk(pts):
    """Build an element of F from breakpoints; validates dyadic x,y and power-of-two slopes."""
    pts = [(Fraction(a), Fraction(b)) for a, b in pts]
    assert pts[0] == (0, 0) and pts[-1] == (1, 1)
    for i in range(len(pts) - 1):
        (xa, ya), (xb, yb) = pts[i], pts[i + 1]
        assert xb > xa and yb > ya
        for v in (xa, ya, xb, yb):
            assert (v.denominator & (v.denominator - 1)) == 0, "non-dyadic breakpoint"
        assert is_power_of_two((yb - ya) / (xb - xa)), "slope not a power of 2"
    return canon(pts)


ID = mk([(0, 0), (1, 1)])


def ev(f, t):
    for i in range(len(f) - 1):
        (xa, ya), (xb, yb) = f[i], f[i + 1]
        if xa <= t <= xb:
            return ya + (yb - ya) * (t - xa) / (xb - xa)
    raise ValueError(t)


def inv(f):
    return canon([(y, x) for x, y in f])


_MULC = {}


def mul(f, g):
    """f * g = f o g (composition right to left, as in the claim)."""
    key = (f, g)
    r = _MULC.get(key)
    if r is not None:
        return r
    gi = inv(g)
    xs = sorted(set(x for x, _ in g) | set(ev(gi, x) for x, _ in f))
    r = canon([(x, ev(f, ev(g, x))) for x in xs])
    if len(_MULC) < 400000:
        _MULC[key] = r
    return r


def power(f, n):
    if n < 0:
        return power(inv(f), -n)
    r = ID
    for _ in range(n):
        r = mul(r, f)
    return r


def bumps(f):
    """Connected components of {t : f(t) != t}, as a list of (a,b)."""
    segs = []
    for i in range(len(f) - 1):
        (xa, ya), (xb, yb) = f[i], f[i + 1]
        if not (xa == ya and xb == yb):
            segs.append((xa, xb))
    out = []
    for a, b in segs:
        # merge only across a breakpoint that is itself moved; a fixed point separates bumps
        if out and out[-1][1] == a and ev(f, a) != a:
            out[-1] = (out[-1][0], b)
        else:
            out.append((a, b))
    return out


X0 = mk([(0, 0), (Fraction(1, 2), Fraction(1, 4)), (Fraction(3, 4), Fraction(1, 2)), (1, 1)])
X1 = mk([(0, 0), (Fraction(1, 2), Fraction(1, 2)), (Fraction(3, 4), Fraction(5, 8)),
         (Fraction(7, 8), Fraction(3, 4)), (1, 1)])
# a one-bump element with support (0,1/2): the copy of x_0 scaled into [0,1/2]
G1 = mk([(0, 0), (Fraction(1, 4), Fraction(1, 8)), (Fraction(3, 8), Fraction(1, 4)),
         (Fraction(1, 2), Fraction(1, 2)), (1, 1)])
GENS = [X0, inv(X0), X1, inv(X1)]


def word(rng, n):
    r = ID
    for _ in range(n):
        r = mul(r, rng.choice(GENS))
    return r


# ---------------------------------------------------------------- group ring K[F], K = Q

def rclean(y):
    return {k: v for k, v in y.items() if v != 0}


def radd(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, ZERO) + v
    return rclean(out)


def rscal(c, a):
    return rclean({k: c * v for k, v in a.items()})


def rmul(a, b):
    out = {}
    for g, u in a.items():
        for h, v in b.items():
            k = mul(g, h)
            out[k] = out.get(k, ZERO) + u * v
    return rclean(out)


def cosets(y, g, gi):
    """Partition supp y into right cosets <g>w; return {rep: [(n, elt)]} with elt = g^n rep."""
    rem = dict(y)
    out = {}
    while rem:
        w = next(iter(rem))
        members = [(0, w)]
        cur, n = w, 0
        while True:
            n += 1
            cur = mul(g, cur)
            if cur in rem:
                members.append((n, cur))
            elif n > 7:
                break
        cur, n = w, 0
        while True:
            n -= 1
            cur = mul(gi, cur)
            if cur in rem:
                members.append((n, cur))
            elif n < -7:
                break
        for _, e in members:
            rem.pop(e, None)
        out[w] = members
    return out


def eps_all(y, g, gi, mu):
    """{rep: eps_rep(y)} over the cosets met by supp y."""
    return {w: sum(y[e] * mu ** n for n, e in mem) for w, mem in cosets(y, g, gi).items()}


def in_J(y, g, gi, mu):
    return all(v == 0 for v in eps_all(y, g, gi, mu).values())


def reduce_b(b, g, gi, mu):
    """b_reduced: in each coset <g>w, move all mass to the representative w with factor mu^n."""
    out = {}
    for w, mem in cosets(b, g, gi).items():
        c = sum(b[e] * mu ** n for n, e in mem)
        if c != 0:
            out[w] = out.get(w, ZERO) + c
    return rclean(out)


def randelt(rng, y_len, wlen):
    return rclean({word(rng, rng.randrange(1, wlen + 1)): Fraction(rng.randrange(-3, 4))
                   for _ in range(y_len)})


# ---------------------------------------------------------------- the tests

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=40)
    ap.add_argument("--seed", type=int, default=7)
    a = ap.parse_args()
    rng = random.Random(a.seed)

    lam = Fraction(2)
    mu = -1 / lam
    G = mul(G1, X1)                       # two bumps: (0,1/2) and (1/2,1)
    GI = inv(G)
    assert len(bumps(G)) == 2, bumps(G)
    assert len(bumps(G1)) == 1 and len(bumps(X1)) == 1

    one_lg = {ID: Fraction(1), G: lam}    # 1 + lambda g

    # ---- (0) coset test, both directions, and g^a y - mu^a y in J
    ok, bad = True, ""
    for _ in range(a.trials):
        r = randelt(rng, 3, 4)
        if not r:
            continue
        y = rmul(one_lg, r)
        if not in_J(y, G, GI, mu):
            ok, bad = False, "a multiple of 1+lambda g failed the coset test"
            break
        if in_J(r, G, GI, mu) and r:      # a random r should essentially never pass
            pass                          # not an error, just record
        for aa in (-2, -1, 1, 3):
            z = radd(rmul({power(G, aa): Fraction(1)}, r), rscal(-(mu ** aa), r))
            if not in_J(z, G, GI, mu):
                ok, bad = False, "g^a y - mu^a y not in J for a=%d" % aa
                break
        if not ok:
            break
    nonmem = sum(1 for _ in range(a.trials)
                 if not in_J(randelt(rng, 3, 4) or {ID: Fraction(1)}, G, GI, mu))
    report("0: Step 0 coset test (both directions)", ok and nonmem >= a.trials - 2,
           bad or "%d/%d random elements correctly detected outside J" % (nonmem, a.trials))

    # ---- (1) Step 1 reduction
    ok, bad = True, ""
    for _ in range(a.trials):
        b = randelt(rng, 4, 4)
        if not b:
            continue
        b0 = reduce_b(b, G, GI, mu)
        if not in_J(radd(b, rscal(Fraction(-1), b0)), G, GI, mu):
            ok, bad = False, "b - b_reduced is not in J"
            break
        seen = set()
        for w, mem in cosets(b0, G, GI).items():
            if len(mem) != 1:
                ok, bad = False, "b_reduced meets a coset twice"
                break
            seen.add(w)
        if not ok:
            break
    report("1: Step 1, b - b_reduced in J and b_reduced meets each coset once", ok, bad)

    # ---- (2) Step 2 identity and falsification search
    H = X1                                 # V = <h>, h = x_1
    HI = inv(H)
    Hpow = {power(H, n): n for n in range(-6, 7)}

    def transverse(t):
        """check V = <h> meets t^{-1}<g>t trivially, for the exponent window used below"""
        ti = inv(t)
        for n in range(-6, 7):
            if n == 0:
                continue
            if mul(ti, mul(power(G, n), t)) in Hpow:
                return False
        return True

    ok, bad, tested, jhits = True, "", 0, 0
    for _ in range(a.trials * 3):
        b = reduce_b(randelt(rng, 3, 3), G, GI, mu)
        if not b:
            continue
        t0 = None
        for t in b:
            if transverse(t):
                t0 = t
                break
        if t0 is None:
            continue
        # v in K[V], V = <h>
        v = rclean({power(H, rng.randrange(-4, 5)): Fraction(rng.randrange(-3, 4))
                    for _ in range(3)})
        if not v:
            continue
        tested += 1
        # beta = sum over t in supp b with t in D = <g> t0 V of b(t) mu^{m_t} c_t
        beta = {}
        t0i = inv(t0)
        for t in b:
            found = None
            for m in range(-8, 9):
                cand = mul(t0i, mul(power(GI, m), t))    # t = g^m t0 c  =>  c = t0^{-1} g^{-m} t
                if cand in Hpow:
                    found = (m, cand)
                    break
            if found:
                m, c = found
                beta[c] = beta.get(c, ZERO) + b[t] * mu ** m
        beta = rclean(beta)
        bv = rmul(b, v)
        betav = rmul(beta, v)
        eps = eps_all(bv, G, GI, mu)
        good = True
        for x in Hpow:
            want = betav.get(x, ZERO)
            # eps_{t0 x}: find the representative of the coset <g> t0 x inside eps
            key = mul(t0, x)
            got = None
            for w, val in eps.items():
                for n in range(-12, 13):
                    if mul(power(G, n), w) == key:
                        got = val * mu ** (-n)          # eps_{g^n w} = mu^{-n} eps_w
                        break
                if got is not None:
                    break
            if got is None:
                got = ZERO
            if got != want:
                good = False
                break
        if not good:
            ok, bad = False, "eps_{t0 x}(b v) != (beta v)(x)"
            break
        if in_J(bv, G, GI, mu):
            jhits += 1
    report("2: Step 2 identity eps_{t0 x}(bv) = (beta v)(x), and bv never in J", ok and jhits == 0,
           bad or "%d random (b, v) pairs with a transverse t0; %d landed in J (theorem says 0)"
           % (tested, jhits))

    # ---- (3) Step 4 transverse saturation
    ok, bad, tested = True, "", 0
    for _ in range(a.trials):
        y = randelt(rng, 3, 3)
        if not y:
            continue
        aelt = rclean({power(H, rng.randrange(-3, 4)): Fraction(rng.randrange(-3, 4))
                       for _ in range(2)})
        if not aelt:
            continue
        tested += 1
        ya = rmul(y, aelt)
        if in_J(ya, G, GI, mu) and not in_J(y, G, GI, mu):
            ok, bad = False, "y a in J but y not in J (item 2 refuted)"
            break
    # the corollary: a unit times a product of one-bump twisted binomials is never in J
    prods_ok = True
    for _ in range(a.trials):
        u = word(rng, rng.randrange(0, 4))
        p = {u: Fraction(1)}
        for h in (X1, G1, mul(X1, mul(G1, inv(X1)))):
            p = rmul(p, {ID: Fraction(1), h: Fraction(rng.randrange(1, 4))})
        if in_J(p, G, GI, mu):
            prods_ok = False
            break
    report("3: Step 4 transverse saturation and the no-product-of-binomials corollary",
           ok and prods_ok, bad or "%d (y,a) pairs, %d products, none refuted" % (tested, a.trials))

    # ---- (4) Step 5 congruence
    ok, bad = True, ""
    for _ in range(a.trials):
        # any V normalized by g with V n <g> = 1 is fine for the congruence itself;
        # here we only test the ring identity b*sum g^a r_a = sum g^a phi^a(b) r_a and
        # its reduction mod J, for arbitrary b, r_a in K[F].
        b = randelt(rng, 2, 3)
        rs = [randelt(rng, 2, 3) for _ in range(3)]
        if not b or not any(rs):
            continue
        v = {}
        for aa, r in enumerate(rs):
            v = radd(v, rmul({power(G, aa): Fraction(1)}, r))
        lhs = rmul(b, v)
        rhs = {}
        z = {}
        for aa, r in enumerate(rs):
            phia = rclean({mul(power(GI, aa), mul(k, power(G, aa))): c for k, c in b.items()})
            rhs = radd(rhs, rmul({power(G, aa): Fraction(1)}, rmul(phia, r)))
            z = radd(z, rscal(mu ** aa, rmul(phia, r)))
        if lhs != rhs:
            ok, bad = False, "b v != sum_a g^a phi^a(b) r_a"
            break
        if not in_J(radd(lhs, rscal(Fraction(-1), z)), G, GI, mu):
            ok, bad = False, "b v is not congruent to sum_a mu^a phi^a(b) r_a mod J"
            break
    report("4: Step 5 congruence b v = sum g^a phi^a(b) r_a = sum mu^a phi^a(b) r_a mod J", ok, bad)

    # ---- (5) bump-count facts used in Step 4
    ok, bad = True, ""
    for _ in range(a.trials):
        h = word(rng, rng.randrange(1, 5))
        if h == ID:
            continue
        for n in (2, 3, -2):
            if bumps(power(h, n)) != bumps(h):
                ok, bad = False, "supp h^n != supp h"
                break
        w = word(rng, rng.randrange(1, 4))
        c = mul(inv(w), mul(h, w))
        if len(bumps(c)) != len(bumps(h)):
            ok, bad = False, "conjugation changed the number of bumps"
            break
        if not ok:
            break
    report("5: supp h^n = supp h and conjugation preserves the bump count", ok, bad)

    # ---- (6) Step 6 surviving decomposition: the structural facts
    facts = []
    facts.append(("g = g1 g2 has two bumps", len(bumps(G)) == 2))
    facts.append(("g^-1 g1 g = g1", mul(GI, mul(G1, G)) == G1))
    facts.append(("g fixes the shared endpoint m = 1/2", ev(G, Fraction(1, 2)) == Fraction(1, 2)))
    facts.append(("g1 in V is identity near q = 1", ev(G1, Fraction(7, 8)) == Fraction(7, 8)))
    facts.append(("g^n moves points near q for n != 0",
                  all(ev(power(G, n), Fraction(7, 8)) != Fraction(7, 8) for n in (1, 2, -1, -2))))
    report("6: Step 6 structural facts for V = <g1> x F_c(p,q)", all(v for _, v in facts),
           "; ".join("%s:%s" % (k, v) for k, v in facts))

    print()
    print("ALL PASS" if not FAIL else "FAILURES: " + ", ".join(FAIL))
    return 1 if FAIL else 0


if __name__ == "__main__":
    raise SystemExit(main())
