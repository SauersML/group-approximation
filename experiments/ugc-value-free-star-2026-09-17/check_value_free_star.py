#!/usr/bin/env python3
"""Checks for research/value-free-star-list-references-put-np-in-rp.

Part A  Step 3-4 chain of Theorem CLV on random toy outer games, computed
        exactly (no sampling): arbitrary labelling lambda (no value
        condition), good-star mass g_a <= Pr_{b~mu(.|a)}[C_ab], decoder
        q_a >= kappa g_a with adversarial wrong labels, B-rule
        lambda_b = pi_{a'b}(hat lambda_{a'}) with a' ~ rho(.|b).
        Checks  E val >= (E_rho q 1_C)^2 >= ((kappa/K1) E_rhoA[g]^2)^2.
Part B  DKKMS validity ratio Pr[valid|U,V]/Pr[valid|U] <= 1/(1-2^(l-k)),
        exactly via Gaussian binomials, with a brute-force check of the
        subspace-avoidance count for small dimensions.
Part C  Local-fix labelling value (1 - beta delta/3)^k at beta = loglogk/k:
        exact formula plus Monte Carlo on disjoint 3LIN tuples.
Deterministic (fixed seeds).  Prints PASS/FAIL per part.
"""
import itertools
import math
import random


# ---------------------------------------------------------------- Part A
def part_a(trials=300, seed=1):
    rng = random.Random(seed)
    fails = 0
    worst = float("inf")
    for _ in range(trials):
        nA, nB, R = rng.randint(2, 6), rng.randint(2, 5), rng.randint(2, 4)
        LA = 2 * R  # A-labels project 2-to-1 onto B-labels
        # outer law rho on A x B (full support for simplicity)
        w = [[rng.random() + 0.05 for _ in range(nB)] for _ in range(nA)]
        Z = sum(map(sum, w))
        rho = [[x / Z for x in row] for row in w]
        rhoA = [sum(row) for row in rho]
        rhoB = [sum(rho[a][b] for a in range(nA)) for b in range(nB)]
        # mu(b|a): perturb rho(b|a) by factor in [1/2, 2] and renormalise
        mu = []
        for a in range(nA):
            v = [rho[a][b] / rhoA[a] * rng.uniform(0.5, 2.0) for b in range(nB)]
            s = sum(v)
            mu.append([x / s for x in v])
        K1 = max(mu[a][b] / (rho[a][b] / rhoA[a])
                 for a in range(nA) for b in range(nB))
        # projections pi_ab : [LA] -> [R], random 2-to-1
        pi = {}
        for a in range(nA):
            for b in range(nB):
                img = list(range(R)) * 2
                rng.shuffle(img)
                pi[a, b] = img
        # ARBITRARY labelling lambda (no value condition)
        lamA = [rng.randrange(LA) for _ in range(nA)]
        lamB = [rng.randrange(R) for _ in range(nB)]
        C = [[pi[a, b][lamA[a]] == lamB[b] for b in range(nB)] for a in range(nA)]
        cprime = [sum(mu[a][b] for b in range(nB) if C[a][b]) for a in range(nA)]
        g = [rng.uniform(0, 1) * cprime[a] for a in range(nA)]
        kappa = rng.uniform(0.05, 1.0)
        q = [min(1.0, kappa * g[a] * rng.uniform(1.0, 1.5)) for a in range(nA)]
        # decoder law at a: lamA[a] w.p. q_a, else an adversarial wrong
        # label (worst for the analysis: a label whose projection is never
        # lamB, when one exists), chosen per vertex
        law = []
        for a in range(nA):
            d = [0.0] * LA
            d[lamA[a]] += q[a]
            wrong = [s for s in range(LA) if s != lamA[a]]
            s_bad = rng.choice(wrong)
            d[s_bad] += 1 - q[a]
            law.append(d)
        # exact expected value of the decoded labelling
        Ev = 0.0
        for b in range(nB):
            for a in range(nA):
                if rho[a][b] == 0:
                    continue
                for a2 in range(nA):
                    r2 = rho[a2][b] / rhoB[b]
                    if a2 == a:
                        p = sum(law[a][s] for s in range(LA)
                                if pi[a, b][s] == pi[a, b][s])
                    else:
                        p = 0.0
                        for s in range(LA):
                            for s2 in range(LA):
                                if pi[a, b][s] == pi[a2, b][s2]:
                                    p += law[a][s] * law[a2][s2]
                    Ev += rho[a][b] * r2 * p
        mid = sum(rho[a][b] * q[a] * C[a][b]
                  for a in range(nA) for b in range(nB))
        EgA = sum(rhoA[a] * g[a] for a in range(nA))
        low = (kappa / K1) * EgA ** 2
        ok = Ev >= mid ** 2 - 1e-12 and mid >= low - 1e-12
        if not ok:
            fails += 1
        if low > 0:
            worst = min(worst, Ev / low ** 2)
    print(f"A: {trials} toy games, fails={fails}, min E val/((kappa/K1)E g^2)^2 = {worst:.3f}")
    return fails == 0


# ---------------------------------------------------------------- Part B
def gbin(n, r):
    """Gaussian binomial [n choose r]_2."""
    if r < 0 or r > n:
        return 0
    num = den = 1
    for i in range(r):
        num *= 2 ** (n - i) - 1
        den *= 2 ** (i + 1) - 1
    return num // den


def p_avoid(n, t, r):
    """Pr[ uniform r-subspace of F_2^n meets a fixed t-subspace only in 0 ]."""
    if r + t > n:
        return 0.0
    return 2 ** (r * t) * gbin(n - t, r) / gbin(n, r)


def brute_avoid(n, t, r):
    """Brute force over all r-subspaces of F_2^n (small n only)."""
    vecs = list(range(1, 2 ** n))
    H = set(range(2 ** t))  # span of the first t coordinates (low bits)
    subs = set()
    for basis in itertools.combinations(vecs, r):
        span = {0}
        for v in basis:
            span |= {x ^ v for x in span}
        if len(span) == 2 ** r:
            subs.add(frozenset(span))
    good = sum(1 for S in subs if not (S - {0}) & (H - {0}))
    return good / len(subs), len(subs)


def part_b():
    ok = True
    # brute-force check of the formula
    for n in range(2, 6):
        for t in range(0, n + 1):
            for r in range(1, n + 1):
                bf, cnt = brute_avoid(n, t, r)
                fm = p_avoid(n, t, r)
                if abs(bf - fm) > 1e-12:
                    ok = False
                    print(f"B: formula mismatch n={n} t={t} r={r}: {bf} vs {fm}")
    print("B: Gaussian-binomial avoidance formula matches brute force for n<=5:", ok)
    worst_ratio_slack = float("inf")
    rows = []
    for l in range(2, 5):
        for k in range(l + 1, 16):
            S_over_N = (2 ** (3 * k) - 2 ** (l - 1 + k)) / (2 ** (3 * k) - 2 ** (l - 1))
            betas = [0.5, 0.2, 0.05]
            if k >= 3:
                betas.append(math.log(math.log(k)) / k if math.log(k) > 1 else 0.05)
            for beta in betas:
                pv = [p_avoid(2 * t + k, t, l - 1) * S_over_N for t in range(k + 1)]
                pt = [math.comb(k, t) * (1 - beta) ** t * beta ** (k - t)
                      for t in range(k + 1)]
                pU = sum(a * b for a, b in zip(pv, pt))
                K1 = max(pv) / pU
                bound = 1 / (1 - 2 ** (l - k))
                # also the lower bound min_t Pr[valid|t] >= 1 - 2^(l-k)
                if K1 > bound + 1e-12 or min(pv) < 1 - 2 ** (l - k) - 1e-12:
                    ok = False
                    print(f"B: FAIL l={l} k={k} beta={beta}: K1={K1} bound={bound}")
                worst_ratio_slack = min(worst_ratio_slack, bound - K1)
                if beta == 0.2 and k in (l + 1, l + 3, 12):
                    rows.append((l, k, K1, bound))
    for l, k, K1, bound in rows:
        print(f"B: l={l} k={k:2d} beta=0.2  K1={K1:.6f}  <= 1/(1-2^(l-k))={bound:.6f}")
    print(f"B: min slack bound-K1 over grid = {worst_ratio_slack:.2e}")
    return ok


# ---------------------------------------------------------------- Part C
def local_fix_mc(k, beta, delta, samples, rng):
    """Monte Carlo value of the local-fix labelling on disjoint 3LIN tuples.

    Each of the k equations of U is violated by y independently w.p. delta.
    lambda_U flips the first variable of each violated equation of U.
    V keeps an equation whole w.p. 1-beta, else one uniform variable of it.
    lambda_V = y|_V with the same canonical fix on every whole violated
    equation.  The edge (U,V) is consistent iff no kept single variable is
    a flipped one.
    """
    good = 0
    for _ in range(samples):
        ok = True
        for _ in range(k):
            viol = rng.random() < delta
            whole = rng.random() >= beta
            if viol and not whole and rng.randrange(3) == 0:
                ok = False
        good += ok
    return good / samples


def part_c():
    rng = random.Random(7)
    ok = True
    for k in (16, 64, 256, 1024):
        beta = math.log(math.log(k)) / k
        for kd in (0.1, 0.5):  # k * delta, i.e. eps_out(y) ~ 1 - e^(-k delta)
            delta = kd / k
            exact = (1 - beta * delta / 3) ** k
            mc = local_fix_mc(k, beta, delta, 4000, rng)
            eps_out = 1 - (1 - delta) ** k
            loss = 1 - exact
            print(f"C: k={k:4d} beta={beta:.4f} eps_out(y)={eps_out:.3f} "
                  f"local-fix loss={loss:.2e} (MC {1 - mc:.2e})")
            if abs(mc - exact) > 0.02:
                ok = False
    return ok


if __name__ == "__main__":
    ra = part_a()
    print("Part A:", "PASS" if ra else "FAIL")
    rb = part_b()
    print("Part B:", "PASS" if rb else "FAIL")
    rc = part_c()
    print("Part C:", "PASS" if rc else "FAIL")
    print("ALL:", "PASS" if (ra and rb and rc) else "FAIL")
