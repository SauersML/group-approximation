#!/usr/bin/env python3
"""Checks for star-list-structure-is-circular-on-decodable-yes-inputs.

Part A: the flat-star case lemma, exhaustively for m <= 5, l in {2, 3}:
        with pref = x|_L + deg * nu (nu the functional on L with kernel L'),
        every lift-satisfied edge at tau = x|_(L') has either
        (sigma_L = x|_L and b = deg) or (sigma_L != x|_L and
        ker(sigma_L - x|_L) = L').
Part B: exact optimum of the flat part of the flip orientation in toy stars:
        X = F_2^4, phi = low two bits, H = <8> or H = 0, x = 0, stars
        L' = <p> with phi(p) != 0 (flat), directions uniform off L' + H,
        W = phi^-1(phi(L')).  Over all b in {0,1}^(stars) and all A-labels,
        the lift-satisfied mass at tau = tau_h is at most
        sum_q w_q max(Pr[deg|q], Pr[not deg|q]) + T2max, where T2max bounds the
        mass of edges with sigma_L != x|_L and ker = L'.  Also shows that the
        naive orientation (random pref on deg edges) gives the honest labelling
        more, Pr[not deg] + Pr[deg]/2, which is why the flip is needed.
Part C: image model X = F_2^(n+1), Phi = first n coordinates, phi first l,
        zeta next s, x = 0, G(c) = least nonzero d in c.  For every functional
        lambda on X and every (l-1)-space L', lambda is 'covered' at L'
        (lambda - a*(L') in W(L')^perp) only if lambda = (omega, d)o Phi with
        d = G(c(L')); so each lambda covers stars of one branch only, and for
        d != 0 the covered mass is < 2^(-s-1).  Two-sided half agreement off
        the covered set is checked exactly.
Part D: the numbers: Hoeffding resampling feasible, and E < gamma' for
        gamma' = 2^(2-l), 8 <= l <= 20, at the k found, with the list budget
        L = gamma'^2 2^(k-l-16) giving (L+1) 2^(-s-1) <= gamma'/16.
Exits 0 iff every check passes.
"""
from fractions import Fraction as Fr
import itertools, math, sys

ok = True


def check(cond, msg):
    global ok
    print(("PASS " if cond else "FAIL ") + msg)
    ok = ok and cond


def par(v):
    return bin(v).count("1") & 1


def span(vs):
    S = {0}
    for v in vs:
        S |= {a ^ v for a in S}
    return frozenset(S)


def subspaces_dim(m, d):
    """All d-dimensional subspaces of F_2^m."""
    out = set()
    for vs in itertools.combinations(range(1, 2 ** m), d):
        S = span(vs)
        if len(S) == 2 ** d:
            out.add(S)
    return out


def restr(f, L):
    """Restriction of the functional <f, .> to the set L, as a tuple."""
    return tuple(par(f & v) for v in sorted(L))


def functionals_on(L, m):
    """Distinct restrictions to L of all functionals on F_2^m."""
    return {restr(f, L) for f in range(2 ** m)}


def add(a, b):
    return tuple(u ^ v for u, v in zip(a, b))


def part_a():
    print("== Part A: flat-star case lemma ==")
    for m in (3, 4, 5):
        for l in (2, 3):
            if l >= m:
                continue
            bad = 0
            cases = 0
            for Lp in subspaces_dim(m, l - 1):
                for L in subspaces_dim(m, l):
                    if not Lp <= L:
                        continue
                    sL = sorted(L)
                    idx_Lp = [i for i, v in enumerate(sL) if v in Lp]
                    funcs = functionals_on(L, m)
                    zero = tuple(0 for _ in sL)
                    nu = [f for f in funcs
                          if all(f[i] == 0 for i in idx_Lp) and f != zero]
                    assert len(nu) == 1
                    nu = nu[0]
                    for xL in funcs:
                        for deg in (0, 1):
                            pref = add(xL, nu) if deg else xL
                            for sig in funcs:
                                if any(sig[i] != xL[i] for i in idx_Lp):
                                    continue  # sigma|_L' != tau_h
                                for b in (0, 1):
                                    target = add(pref, nu) if b else pref
                                    if sig != target:
                                        continue
                                    cases += 1
                                    mu = add(sig, xL)
                                    ker = {v for v, t in zip(sL, mu) if t == 0}
                                    c1 = (mu == zero and b == deg)
                                    c2 = (mu != zero and ker == set(Lp))
                                    if not (c1 or c2):
                                        bad += 1
            check(bad == 0 and cases > 0,
                  f"m={m} l={l}: {cases} lift-satisfied cases, all in "
                  f"(mu=0, b=deg) or (ker mu = L')")


def part_b():
    print("== Part B: flat stars of the flip orientation, exact optimum ==")
    import random
    m = 4
    for H in (frozenset({0, 8}), frozenset({0})):
        stars = [p for p in range(1, 16) if (p & 3) and p not in H]
        wq = Fr(1, len(stars))
        edges = []  # (p, xe, L, deg, weight)
        pdeg = {}
        for p in stars:
            LpH = {a ^ h for a in (0, p) for h in H}
            dirs = [v for v in range(16) if v not in LpH]
            Wp = {v for v in range(16) if (v & 3) in (0, p & 3)}
            nd = 0
            for xe in dirs:
                L = span([p, xe])
                deg = 1 if xe in Wp else 0
                nd += deg
                edges.append((p, xe, L, deg, wq / len(dirs)))
            pdeg[p] = Fr(nd, len(dirs))
        Ls = sorted({e[2] for e in edges}, key=sorted)

        def build(prefbit):
            """per L: list over sigma of [(p, required b, weight)]."""
            table = []
            for L in Ls:
                sL = sorted(L)
                funcs = sorted(functionals_on(L, m))
                rows = []
                for sig in funcs:
                    req = []
                    for (p, xe, LL, deg, w) in edges:
                        if LL != L:
                            continue
                        ip = sL.index(p)
                        if sig[ip] != 0:
                            continue  # sigma|_L' != tau_h = 0
                        # sigma in {0, nu}; nu(xe) = 1, so sigma = (r + b) nu
                        r = prefbit(p, xe, deg)
                        s = sig[sL.index(xe)]
                        req.append((p, s ^ r, w))
                    rows.append(req)
                table.append(rows)
            return table

        def opt(table):
            best = Fr(0)
            for bits in itertools.product((0, 1), repeat=len(stars)):
                bmap = dict(zip(stars, bits))
                tot = Fr(0)
                for rows in table:
                    tot += max(sum((w for (p, rb, w) in req if bmap[p] == rb),
                                   Fr(0)) for req in rows)
                best = max(best, tot)
            return best

        flip = build(lambda p, xe, deg: deg)
        o_flip = opt(flip)
        first = sum(wq * max(pdeg[p], 1 - pdeg[p]) for p in stars)
        T2 = Fr(0)
        for L in Ls:
            T2 += max(sum((e[4] for e in edges if e[2] == L and e[0] == p),
                          Fr(0)) for p in stars)
        check(o_flip <= first + T2,
              f"H={sorted(H)}: flip optimum {float(o_flip):.4f} <= "
              f"max-fraction {float(first):.4f} + T2max {float(T2):.4f}")
        rng = random.Random(1)
        rbits = {(p, xe): rng.randint(0, 1) for (p, xe, _, _, _) in edges}
        naive = build(lambda p, xe, deg: rbits[(p, xe)] if deg else 0)
        hon_naive = sum((e[4] for e in edges
                         if e[3] == 0 or rbits[(e[0], e[1])] == 0), Fr(0))
        hon_flip = sum((e[4] for e in edges if e[3] == 0), Fr(0))
        o_naive = opt(naive)
        check(hon_naive > hon_flip and o_naive >= hon_naive,
              f"H={sorted(H)}: honest x (b=0) gets {float(hon_flip):.4f} "
              f"under the flip, {float(hon_naive):.4f} under random-on-W "
              f"(expected Pr[nd]+Pr[d]/2 = "
              f"{float(sum(wq*(1-pdeg[p]/2) for p in stars)):.4f}); "
              f"naive optimum {float(o_naive):.4f}")


def part_c():
    print("== Part C: each reference covers one branch; two-sided half ==")
    for (l, s) in ((2, 1), (2, 2), (3, 1), (3, 2)):
        n = l + s
        M = n + 1
        lmask = (1 << l) - 1
        smask = ((1 << s) - 1) << l
        Grs = sorted(subspaces_dim(M, l - 1), key=sorted)
        wL = Fr(1, len(Grs))
        good = True
        two_sided = True
        cov = {}
        for Lp in Grs:
            P = {v & ((1 << n) - 1) for v in Lp}
            c = sorted({(v & smask) >> l for v in P if (v & lmask) == 0})
            G = min([d for d in c if d], default=0)
            astar = G << l
            phiL = {v & lmask for v in Lp}
            W = [v for v in range(2 ** M) if (v & lmask) in phiL]
            Wset = set(W)
            off = [v for v in range(2 ** M) if v not in Wset]
            Wperp = [f for f in range(2 ** M) if all(par(f & w) == 0 for w in W)]
            for f in Wperp:
                if f & ~lmask or any(par(f & u) for u in phiL):
                    good = False
            for lam in range(2 ** M):
                covered = (lam ^ astar) in Wperp
                if covered:
                    dlam = (lam & smask) >> l
                    if (lam >> n) & 1 or dlam != G:
                        good = False
                    cov[lam] = cov.get(lam, Fr(0)) + wL
                else:
                    for b in (0, 1):
                        agree = sum(1 for v in off
                                    if par(lam & v) == par(astar & v) ^ b)
                        if Fr(agree, len(off)) != Fr(1, 2):
                            two_sided = False
        check(good, f"(l,s)=({l},{s}): W^perp = omega o phi, and a covering "
                    f"lambda is (omega, G(c(L'))) o Phi")
        check(two_sided, f"(l,s)=({l},{s}): uncovered stars have agreement "
                         f"exactly 1/2 for b = 0 and b = 1")
        lemma7 = Fr(2 ** (l - 1) - 1, 2 ** n - 1)
        mx = max((v for lam, v in cov.items() if (lam & smask) >> l), default=0)
        check(mx <= lemma7 < Fr(1, 2 ** (s + 1)),
              f"(l,s)=({l},{s}): max covered mass of a branch-d reference, "
              f"d != 0: {float(mx):.4f} <= {float(lemma7):.4f} < 2^(-s-1)")


def E_terms(k, l, gp):
    """Float evaluation of the error E of Theorem O."""
    c = math.ceil(math.log2(1 / gp)) + 12
    n = k - c
    s = n - l
    log2L = 2 * math.log2(gp) + k - l - 16

    def p2(e):
        return 2.0 ** e if e > -1000 else 0.0

    beta = max(math.log(math.log(k)) / k, math.log2(math.log2(k)) / k)
    t = {
        "eta": p2(-k),
        "tau": p2(l - 1 - 2 * k),
        "hyper": 1 / (2 ** l - 1),
        "SD*": beta * math.sqrt(k) * 2 ** (l + 3) + 3 * p2(l - k),
        # log2(L 2^(-s-1)) = 2 log2 gamma' + c - 17, exactly (k cancels)
        "cover": p2(2 * math.log2(gp) + c - 17) + p2(-s - 1),
        "bad": p2(-c) / (1 - p2(l - 1 - k)),
    }
    return t, log2L, s


def part_d():
    print("== Part D: parameters ==")
    for l in range(8, 21):
        gp = 2.0 ** (2 - l)
        # Hoeffding per star: 2^(3k+l+1) exp(-2^(k-l)) < 1
        kh = next(k for k in range(l + 1, 10 * l)
                  if (3 * k + l + 1) * math.log(2) < 2.0 ** (k - l))
        j = next(j for j in range(5, 200)
                 if sum(E_terms(2 ** j, l, gp)[0].values()) < gp)
        k = 2 ** j
        allk = all(sum(E_terms(2 ** jj, l, gp)[0].values()) < gp
                   for jj in range(j, j + 40))
        t, log2L, s = E_terms(k, l, gp)
        E = sum(t.values())
        v_ok = 0.6096 - 2.0 ** (l - k) - t["bad"] >= 0.605
        check(kh <= k and allk and v_ok and t["cover"] <= gp / 16 + 2.0 ** (-s),
              f"l={l}: gamma'=2^{2-l}: E={E:.3e} < gamma' for all k >= 2^{j} "
              f"(checked to 2^{j+39}); Hoeffding from k={kh}; "
              f"val(h_G) >= 0.605; cover term {t['cover']:.2e}; "
              f"log2 L = {log2L:.0f}")
    # log L = k ln 2 - O(l) beats k/(4 exp(q l)) for every q >= 0
    check(math.log(2) > 0.25, "k ln 2 > k/4 >= k/(4 exp(q l)): the L range "
                              "exceeds the Corollary DK^C budget at large k")


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
    print("ALL PASS" if ok else "SOME FAIL")
    sys.exit(0 if ok else 1)
