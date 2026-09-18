#!/usr/bin/env python3
"""Regression checks for projective-alphabet-lifts-cannot-amplify-pairing-moments.

Bounded exact checks only; the all-dimensional statements are proved in
research/projective-lift-moment-transfer-proof.md.

Setting. Sigma' = [2n'] (output labels), S = image of a label map p : Sigma' -> S
(|S| = s even), surplus g = 2n' - s.  An output kernel matching lam of Sigma' is
*compatible* with a partial matching pi of S if every pair {x,y} of lam has
p(x) = p(y) or {p(x),p(y)} in pi.  For laws on matchings write
    D(x) = m^(npts/2) * Pr[x constant on every pair],
    ||1_E D||_q^q = m^(-npts) * sum_{x in E} D(x)^q.

1. Transfer inequality (exact, Fractions).  For random couplings (pi, lam) with a
   mixture of several label maps p_i of weights w_i, and E' in {all, a count
   window, a random subset}:
       ||1_E' D_mu'||_q^q >= w_i^q * m^((q-2) g_i / 2) * ||1_E''_i D_{S,i}||_q^q,
   E''_i = {z : z o p_i in E'},  D_{S,i}(z) = m^(s_i/2) Pr[z const on pi | i].
   Also the corollary >= w_i^q * theta_i^q * m^((q-2) g_i / 2).
2. Support count: the number of lam compatible with a fixed pi and p equals
   prod_B (|B|-1)!! over super-blocks and is at most (2n')^(3g/2).
3. Blow-up demo: the fully rich input (uniform law on all matchings of [2n])
   lifted by a doubling map (fibers of size 2, g = 2n) has q-moment growing like
   m^((q-2) n / q), while the uniform law on all matchings of [2n'] does not.
"""
import itertools, math, random
from fractions import Fraction
import numpy as np


def matchings(pts):
    pts = list(pts)
    if not pts:
        yield ()
        return
    a = pts[0]
    for i in range(1, len(pts)):
        rest = pts[1:i] + pts[i + 1:]
        for mm in matchings(rest):
            yield ((a, pts[i]),) + mm


def const_on(x, pairs):
    return all(x[a] == x[b] for a, b in pairs)


def moment_q(law, npts, m, q, E):
    """Exact ||1_E D||_q^q; law = list of (Fraction weight, pairs); pairs may be partial.
    D uses normalisation m^(npts/2) (npts even)."""
    assert npts % 2 == 0
    scale = Fraction(m) ** (npts // 2)
    tot = Fraction(0)
    for x in itertools.product(range(m), repeat=npts):
        if not E(x):
            continue
        P = sum((w for w, pr in law if const_on(x, pr)), Fraction(0))
        tot += (scale * P) ** q
    return tot / Fraction(m) ** npts


def blocks(p, pi, s, npts):
    """Super-blocks of Sigma' for label map p (list) and partial matching pi of S."""
    partner = {}
    for a, b in pi:
        partner[a] = b
        partner[b] = a
    seen, out = set(), []
    for a in range(s):
        if a in seen:
            continue
        grp = {a}
        if a in partner:
            grp.add(partner[a])
        seen |= grp
        out.append([x for x in range(npts) if p[x] in grp])
    return out


def random_compatible(p, pi, s, npts, rng):
    lam = []
    for B in blocks(p, pi, s, npts):
        if len(B) % 2:
            return None
        B = B[:]
        rng.shuffle(B)
        lam += [(B[2 * i], B[2 * i + 1]) for i in range(len(B) // 2)]
    return tuple(lam)


def dfact(k):  # (k-1)!! for even k
    r = 1
    for j in range(k - 1, 0, -2):
        r *= j
    return r


def check_transfer(rng, trials=40):
    count = 0
    for _ in range(trials):
        m = rng.choice([2, 3])
        npts = rng.choice([4, 6]) if m == 3 else rng.choice([4, 6, 8])
        nmaps = rng.choice([1, 2])
        qs = [1, 2, 3, 4]
        maps = []
        for _i in range(nmaps):
            s = rng.choice([v for v in range(2, npts + 1, 2)])
            p = list(range(s)) + [rng.randrange(s) for _ in range(npts - s)]
            rng.shuffle(p)
            maps.append((s, p))
        wts = [Fraction(rng.randint(1, 5)) for _ in maps]
        wsum = sum(wts)
        wts = [w / wsum for w in wts]
        joint = []  # (weight, i, pi, lam)
        for i, (s, p) in enumerate(maps):
            cands = []
            tries = 0
            while len(cands) < 3 and tries < 200:
                tries += 1
                # random perfect matching of a ground set containing S, restricted to S
                ground = list(range(s + 2 * rng.randint(0, 1)))
                rng.shuffle(ground)
                full = [(ground[2 * j], ground[2 * j + 1]) for j in range(len(ground) // 2)]
                pi = tuple((a, b) for a, b in full if a < s and b < s)
                lam = random_compatible(p, pi, s, npts, rng)
                if lam is not None:
                    cands.append((Fraction(rng.randint(1, 4)), pi, lam))
            if not cands:
                return None
            cs = sum(c[0] for c in cands)
            for c in cands:
                joint.append((wts[i] * c[0] / cs, i, c[1], c[2]))
        law_out = [(w, lam) for w, _i, _pi, lam in joint]
        subset_seed = rng.random()

        def counts_ok(x):
            return all(abs(x.count(c) - Fraction(npts, m)) <= 1 for c in range(m))

        def rand_subset(x, _seed=subset_seed):
            return random.Random(hash((x, _seed))).random() < 0.5

        for Ename, E in (("all", lambda x: True), ("window", counts_ok), ("random", rand_subset)):
            for q in qs:
                lhs = moment_q(law_out, npts, m, q, E)
                for i, (s, p) in enumerate(maps):
                    g = npts - s
                    cond = [(w / wts[i], pi) for w, j, pi, _l in joint if j == i]
                    Epp = lambda z, p=p, E=E: E(tuple(z[p[x]] for x in range(npts)))
                    rhs_in = moment_q(cond, s, m, q, Epp)
                    factor = Fraction(m) ** ((q - 2) * g // 2) if (q - 2) * g >= 0 else Fraction(1, m ** ((2 - q) * g // 2))
                    rhs = wts[i] ** q * factor * rhs_in
                    assert lhs >= rhs, (Ename, q, lhs, rhs)
                    # theta corollary: theta = min over pi of Pr_{z const on pi}[z o p in E']
                    theta = None
                    for _w, pi in cond:
                        tot = good = 0
                        for z in itertools.product(range(m), repeat=s):
                            if const_on(z, pi):
                                tot += 1
                                good += Epp(z)
                        val = Fraction(good, tot)
                        theta = val if theta is None else min(theta, val)
                    assert lhs >= wts[i] ** q * theta ** q * factor, (Ename, q)
                    count += 1
    return count


def check_support_count(rng, trials=60):
    n_checked = 0
    for _ in range(trials):
        npts = rng.choice([6, 8, 10])
        s = rng.choice([v for v in range(2, npts + 1, 2)])
        p = list(range(s)) + [rng.randrange(s) for _ in range(npts - s)]
        rng.shuffle(p)
        g = npts - s
        pts = list(range(s))
        rng.shuffle(pts)
        pi = tuple((pts[2 * j], pts[2 * j + 1]) for j in range(s // 2))
        if rng.random() < 0.5 and s >= 2:
            pi = pi[:-1]  # partial: the last two points are matched outside S
        partner = {}
        for a, b in pi:
            partner[a], partner[b] = b, a
        cnt = 0
        for lam in matchings(range(npts)):
            ok = True
            for x, y in lam:
                if not (p[x] == p[y] or partner.get(p[x]) == p[y]):
                    ok = False
                    break
            cnt += ok
        prod = 1
        for B in blocks(p, pi, s, npts):
            prod *= dfact(len(B)) if len(B) % 2 == 0 else 0
        assert cnt == prod, (cnt, prod)
        assert cnt <= npts ** (3 * g / 2) + 1e-9
        n_checked += 1
    return n_checked


def dfo(k):  # (k-1)!! with (-1)!! = 1 for k = 0, and 0 for odd k
    if k % 2:
        return 0
    return dfact(k)


def lift_prob(k0, k1, j, nf):
    """Pr[x const on lam] for the doubling lift [2*nf] -> [nf] of the uniform law on
    matchings of [nf] fibers (lam uniform among compatible matchings), m = 2, where x
    has k0 fibers coloured 00, k1 fibers 11 and j mixed fibers."""
    tot = Fraction(0)
    if j % 2:
        return tot
    for i in range(0, min(k0, k1) + 1):
        if (k0 - i) % 2 or (k1 - i) % 2:
            continue
        ways = math.comb(k0, i) * math.comb(k1, i) * math.factorial(i) * dfo(k0 - i) * dfo(k1 - i) * dfo(j)
        tot += Fraction(ways, 3 ** (i + j // 2))
    return tot / dfact(nf)


def window(c0, npts, kappa):
    return abs(c0 - npts / 2) <= kappa * math.sqrt(npts)


def lift_moment(n, q, kappa):
    """Exact ||1_E D_lift||_q on [4n] (input alphabet [2n]), E = count window, m = 2."""
    nf, npts = 2 * n, 4 * n
    tot = Fraction(0)
    for k0 in range(nf + 1):
        for k1 in range(nf + 1 - k0):
            j = nf - k0 - k1
            if not window(2 * k0 + j, npts, kappa):
                continue
            num = math.factorial(nf) // (math.factorial(k0) * math.factorial(k1) * math.factorial(j)) * 2 ** j
            D = 2 ** (npts // 2) * lift_prob(k0, k1, j, nf)
            tot += num * D ** q
    return float(tot / 2 ** npts) ** (1.0 / q)


def unif_moment(npts, q, E):
    """Exact ||1_E D_unif||_q for the uniform law on all matchings of [npts], m = 2;
    E is a predicate on the number c0 of zeros."""
    tot = Fraction(0)
    for c0 in range(npts + 1):
        if not E(c0):
            continue
        D = Fraction(2 ** (npts // 2) * dfo(c0) * dfo(npts - c0), dfact(npts))
        tot += math.comb(npts, c0) * D ** q
    return float(tot / 2 ** npts) ** (1.0 / q)


def closed_form_cross_check():
    for nf in (2, 4):
        npts = 2 * nf
        p = [x // 2 for x in range(npts)]
        lams = []
        for pi in matchings(range(nf)):
            per_block = [list(matchings(B)) for B in blocks(p, pi, nf, npts)]
            for combo in itertools.product(*per_block):
                lams.append(tuple(e for part in combo for e in part))
        for x in itertools.product(range(2), repeat=npts):
            k0 = sum(1 for a in range(nf) if x[2 * a] == 0 and x[2 * a + 1] == 0)
            k1 = sum(1 for a in range(nf) if x[2 * a] == 1 and x[2 * a + 1] == 1)
            pr = Fraction(sum(const_on(x, l) for l in lams), len(lams))
            assert pr == lift_prob(k0, k1, nf - k0 - k1, nf), (nf, x)
    return True


def blowup_demo(kappa=1.0):
    rows = []
    for n in (4, 8, 16, 32, 64):
        for q in (3, 4):
            lift = lift_moment(n, q, kappa)
            inp = unif_moment(2 * n, q, lambda c0: window(2 * c0, 4 * n, kappa))
            bound = 2 ** ((q - 2) * (2 * n) / (2 * q)) * inp
            uni = unif_moment(4 * n, q, lambda c0: window(c0, 4 * n, kappa))
            assert lift >= bound * (1 - 1e-12)
            rows.append((n, q, lift, bound, inp, uni))
    return rows


if __name__ == "__main__":
    rng = random.Random(20260917)
    c1 = check_transfer(rng)
    print(f"[1] transfer inequality and theta corollary: {c1} exact comparisons passed")
    c2 = check_support_count(rng)
    print(f"[2] compatible-matching count = prod (|B|-1)!! <= (2n')^(3g/2): {c2} cases passed")
    closed_form_cross_check()
    print("[3] closed form for the doubling lift matches enumeration at 2n = 2, 4")
    print("    doubling lift of the fully rich law on [2n] to [4n], m = 2, E = {|#0 - 2n| <= sqrt(4n)}")
    print("     n  q   ||1_E D_lift||_q   2^((q-2)n/q)||1_E'' D_in||_q   ||1_E'' D_in||_q   ||1_E D_unif[4n]||_q")
    for n, q, lift, bound, inp, uni in blowup_demo():
        print(f"    {n:2d}  {q}   {lift:14.4f}   {bound:26.4f}   {inp:15.4f}   {uni:19.4f}")
    print("ALL CHECKS PASSED")
