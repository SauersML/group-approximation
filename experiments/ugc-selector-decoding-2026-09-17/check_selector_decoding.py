#!/usr/bin/env python3
"""Checks for efficient-branch-selectors-list-decode-honest-outer-labels.

Part A (exhaustive).  2-to-2 Grassmann constraints over F_2^m, m=4, l=2, and
the 2-to-1 restriction constraints L -> H.  Every orientation (one perfect
matching per K_{2,2} block, resp. one preimage per fiber) is a bijection.  An
honest labelling sigma satisfies the oriented edge iff
g_e(sigma|H) = <sigma, x'> + <sigma, x>, where g_e is the per-block bit
of the orientation.  So the branch bit of an honest labelling is a prediction
of the linear form <sigma, x'> from the seed label.

Part B (random).  Fourier step: a randomized predictor with advantage beta
under a distribution tau-close to uniform has hat F(sigma) >= 2 beta - 2 tau,
and at most 4/gamma^2 characters have hat F >= gamma/2.

Part C (random end-to-end).  Toy composed instance: outer projection game,
planted outer labelling with eps violations, selectors whose honest
advantage profile averages gamma, with adversarial decoy predictions on
wrong seed guesses.  The decoder of the proof is run, and the decoded
labelling's expected outer value is compared with p^2 - 2 eps,
p = gamma^3 2^{-l} / 4.
"""
import itertools
import random

# ---------------------------------------------------------------- utilities


def dot(a, x):
    return bin(a & x).count("1") & 1


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {u ^ v for u in s}
    return frozenset(s)


def subspaces(m, k):
    seen = set()
    for vecs in itertools.combinations(range(1, 1 << m), k):
        sp = span(vecs)
        if len(sp) == 1 << k:
            seen.add(sp)
    return sorted(seen, key=lambda s: sorted(s))


# ------------------------------------------------------------------ part A


def part_a(m=4, l=2):
    L_all = subspaces(m, l)
    checked = 0
    for L0 in L_all:
        for L1 in L_all:
            H = L0 & L1
            if len(H) != 1 << (l - 1):
                continue
            x0 = min(L0 - H)  # representative of L0 \ H
            x1 = min(L1 - H)
            Hb = sorted(H)
            # labels: linear forms on L are identified with sigma mod L^perp;
            # we work with full sigma in F_2^m and restrict by evaluation.
            def restrict(sig, L):
                return tuple(dot(sig, v) for v in sorted(L))

            labels0 = sorted({restrict(s, L0) for s in range(1 << m)})
            labels1 = sorted({restrict(s, L1) for s in range(1 << m)})
            assert len(labels0) == 1 << l and len(labels1) == 1 << l
            # a label on L is determined by its restriction to H and value at x
            idx0 = {restrict(s, L0): (restrict(s, H), dot(s, x0)) for s in range(1 << m)}
            idx1 = {restrict(s, L1): (restrict(s, H), dot(s, x1)) for s in range(1 << m)}
            blocks = sorted({idx0[t][0] for t in labels0})
            assert len(blocks) == 1 << (l - 1)
            # orientation: g : blocks -> bit; matching s <-> t with
            # t(x1) = s(x0) xor g(s|H)
            for gbits in itertools.product((0, 1), repeat=len(blocks)):
                g = dict(zip(blocks, gbits))
                match = {}
                for t0 in labels0:
                    h, b0 = idx0[t0]
                    for t1 in labels1:
                        h1, b1 = idx1[t1]
                        if h1 == h and b1 == b0 ^ g[h]:
                            match.setdefault(t0, []).append(t1)
                # bijection inside the 2-to-2 constraint
                assert all(len(v) == 1 for v in match.values())
                assert len({v[0] for v in match.values()}) == 1 << l
                for sig in range(1 << m):
                    s0 = restrict(sig, L0)
                    s1 = restrict(sig, L1)
                    sat = match[s0][0] == s1
                    pred = dot(sig, x0) ^ g[restrict(sig, H)]
                    assert sat == (pred == dot(sig, x1))
                    checked += 1
        # 2-to-1 restriction constraint L0 -> H, one preimage per fiber
        for H in subspaces(m, l - 1):
            if not H <= L0:
                continue
            x0 = min(L0 - H)
            fibers = {}
            for s in range(1 << m):
                fibers.setdefault(tuple(dot(s, v) for v in sorted(H)), set()).add(
                    tuple(dot(s, v) for v in sorted(L0)))
            for fib in fibers.values():
                assert len(fib) == 2
            blocks = sorted(fibers)
            for gbits in itertools.product((0, 1), repeat=len(blocks)):
                g = dict(zip(blocks, gbits))
                for sig in range(1 << m):
                    h = tuple(dot(sig, v) for v in sorted(H))
                    chosen = [t for t in fibers[h]
                              if t[sorted(L0).index(x0)] == g[h]]
                    assert len(chosen) == 1
                    sat = chosen[0] == tuple(dot(sig, v) for v in sorted(L0))
                    assert sat == (g[h] == dot(sig, x0))
                    checked += 1
    return checked


# ------------------------------------------------------------------ part B


def fourier(Fvals, m):
    n = 1 << m
    return [sum(Fvals[x] * (1 - 2 * dot(a, x)) for x in range(n)) / n for a in range(n)]


def part_b(trials=300, m=6, seed=1):
    rng = random.Random(seed)
    n = 1 << m
    worst_margin = 1e9
    for _ in range(trials):
        sigma = rng.randrange(n)
        gamma = rng.uniform(0.05, 0.5)
        # distribution D: uniform on a random subset missing a tau fraction
        missing = set(rng.sample(range(n), rng.randrange(0, max(1, int(n * gamma / 4)))))
        support = [x for x in range(n) if x not in missing]
        tau = len(missing) / n
        # randomized predictor: P(x) = Pr[predict 1]
        P = {}
        for x in range(n):
            P[x] = rng.random()
        # tilt toward sigma to create advantage
        tilt = rng.uniform(0, 1)
        for x in support:
            P[x] = (1 - tilt) * P[x] + tilt * dot(sigma, x)
        beta = sum((P[x] if dot(sigma, x) else 1 - P[x]) for x in support) / len(support) - 0.5
        Fvals = [0.0] * n
        for x in support:
            Fvals[x] = 1 - 2 * P[x]  # E[(-1)^prediction]
        hat = fourier(Fvals, m)
        # claim: hat F(sigma) >= 2 beta - 2 tau
        worst_margin = min(worst_margin, hat[sigma] - (2 * beta - 2 * tau))
        assert hat[sigma] >= 2 * beta - 2 * tau - 1e-12
        big = [a for a in range(n) if hat[a] >= gamma / 2]
        assert len(big) <= 4 / gamma ** 2 + 1e-9
    return worst_margin


# ------------------------------------------------------------------ part C


def part_c(trials=40, seed=7):
    rng = random.Random(seed)
    results = []
    for _ in range(trials):
        m, mp, l = 5, 3, 2
        n = 1 << m
        NA, NB, deg = 12, 6, 4
        eps = rng.choice([0.0, 0.02, 0.05])
        gamma = rng.choice([0.25, 0.35, 0.45])
        lam = [rng.randrange(1, n) for _ in range(NA)]
        lamB = [rng.randrange(1 << mp) for _ in range(NB)]

        def app(M, v):
            return sum(dot(r, v) << i for i, r in enumerate(M))

        proj = {}
        outer = []
        for b in range(NB):
            for a in rng.sample(range(NA), deg):
                target = lamB[b] if rng.random() >= eps else rng.randrange(1 << mp)
                M = []
                fix = next(v for v in range(n) if dot(v, lam[a]) == 1)
                for i in range(mp):
                    r = rng.randrange(n)
                    if dot(r, lam[a]) != (target >> i) & 1:
                        r ^= fix
                    M.append(r)
                proj[(a, b)] = M
                outer.append((a, b))
        viol = sum(app(proj[e], lam[e[0]]) != lamB[e[1]] for e in outer) / len(outer)
        # inner edges: seed w = (a_seed, subspace id), target a, direction x
        seeds = [(rng.randrange(NA), j) for j in range(3)]
        seedlab = {w: rng.randrange(1 << l) for w in seeds}  # honest seed label
        edges = []
        # advantage profile: beta_{w,a} in {1/2, 0}, mass fraction 2 gamma good
        for w in seeds:
            for a in range(NA):
                good = rng.random() < 2 * gamma
                pred_table = {}
                decoy = rng.randrange(n)
                for s in range(1 << l):
                    for x in range(n):
                        if s == seedlab[w]:
                            pred_table[(s, x)] = dot(lam[a], x) if good else rng.randrange(2)
                        else:
                            pred_table[(s, x)] = dot(decoy ^ s, x)
                edges.append((w, a, pred_table))
        lift = sum(sum(t[(seedlab[w], x)] == dot(lam[a], x) for x in range(n)) / n
                   for (w, a, t) in edges) / len(edges)
        g_eff = lift - 0.5
        if g_eff <= 0:
            continue
        # decoder: exact decoding probability q_a
        q = []
        lists_ok = True
        for a in range(NA):
            ws = [(w, t) for (w, aa, t) in edges if aa == a]
            tot = 0.0
            for (w, t) in ws:
                for s in range(1 << l):
                    Fv = [1 - 2 * t[(s, x)] for x in range(n)]
                    hat = fourier(Fv, m)
                    L = [al for al in range(n) if hat[al] >= g_eff / 2]
                    if len(L) > 4 / g_eff ** 2:
                        lists_ok = False
                    if L and lam[a] in L:
                        tot += 1 / len(L)
            q.append(tot / (len(ws) * (1 << l)))
        # expected outer value of decoded labelling (independent per a)
        val = 0.0
        for (a, b) in outer:
            nb = [aa for (aa, bb) in outer if bb == b]
            pr = 0.0
            for a2 in nb:
                if a2 == a:
                    pr += q[a]
                else:
                    ok = app(proj[(a, b)], lam[a]) == app(proj[(a2, b)], lam[a2])
                    pr += q[a] * q[a2] if ok else 0.0
            val += pr / len(nb)
        val /= len(outer)
        p = g_eff ** 3 * 2 ** (-l) / 4
        q_nu = sum(q) / NA  # nu_A is uniform here: every a has 3 seed pairs
        q_outer = sum(q[a] for (a, b) in outer) / len(outer)
        assert q_nu >= p - 1e-12
        bound = q_outer ** 2 - 2 * viol
        results.append((val, bound, lists_ok))
        assert lists_ok
        assert val >= bound - 1e-12
    return results


if __name__ == "__main__":
    ca = part_a()
    print("part A: honest branch identity and bijectivity, cases checked:", ca)
    wm = part_b()
    print("part B: Fourier step, worst margin hat F(sigma) - (2beta - 2tau) =", round(wm, 6))
    res = part_c()
    print("part C: end-to-end toy decoder trials:", len(res))
    print("  min (decoded value - bound):", round(min(v - bnd for v, bnd, _ in res), 6))
    print("  min decoded outer value:", round(min(v for v, _, _ in res), 4))
    print("ALL CHECKS PASSED")
