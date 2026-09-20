#!/usr/bin/env python3
"""Check for hastad-images-are-never-robustly-unique.

For W = t variable-disjoint 3-clauses, sigma a satisfying assignment, and
Q = product of one-variable flip pairs on m clauses (both != sigma), check:
  (a) pi_2(T) = {sigma_U} iff not all u_j = d_j  (theta = 3^-m exactly);
  (b) Fourier bias formula (1-2eps)^|T| Pr[pi_2(T)={sigma_U}] vs Monte Carlo
      of the literal Hastad test A(f) B(g) B(h), h = (f o pi) g mu;
  (c) chi_{sigma} and chi_T disagree on half of all g (distance 1/2 per slot);
  (d) Pr[h = +-g] <= 2^(1-2^t);
  (e) Corollary H parameter arithmetic at gamma' = 0.105.
Exit code 0 iff all checks pass.
"""
import itertools
import math
import random
import sys
from collections import Counter

random.seed(20260920)
ok = True


def fail(msg):
    global ok
    ok = False
    print("FAIL:", msg)


def build(t, m):
    # clause j on variables 3j..3j+2; its unique falsifying vertex is unsat[j]
    unsat = [tuple(random.choice((1, -1)) for _ in range(3)) for _ in range(t)]
    blocks = [[a for a in itertools.product((1, -1), repeat=3) if a != unsat[j]]
              for j in range(t)]
    sigma = [random.choice(blocks[j]) for j in range(t)]
    pairs, dvars = [], []
    for j in range(m):
        cand = [(p, q) for p in blocks[j] for q in blocks[j]
                if p < q and p != sigma[j] and q != sigma[j]
                and sum(x != y for x, y in zip(p, q)) == 1]
        if not cand:
            fail("no flip edge in clause %d" % j)
            return None
        p, q = random.choice(cand)
        pairs.append((p, q))
        dvars.append([i for i in range(3) if p[i] != q[i]][0])
    SAT = [sum(c, ()) for c in itertools.product(*blocks)]
    sig = sum(sigma, ())
    Q = []
    for choice in itertools.product((0, 1), repeat=m):
        y = [pairs[j][choice[j]] for j in range(m)] + sigma[m:]
        Q.append(sum(y, ()))
    T = [sig] + Q
    assert len(set(T)) == len(T) == 2 ** m + 1 and set(T) <= set(SAT)
    return SAT, sig, T, dvars


def proj(y, u):
    return tuple(y[3 * j + u[j]] for j in range(len(u)))


def odd_part(ys, u):
    c = Counter(proj(y, u) for y in ys)
    return frozenset(z for z, n in c.items() if n % 2)


def check_block(t, m, eps=0.05):
    b = build(t, m)
    if b is None:
        return
    SAT, sig, T, dvars = b
    Us = list(itertools.product(range(3), repeat=t))
    good = 0
    for u in Us:
        vis = odd_part(T, u) != frozenset([proj(sig, u)])
        alld = all(u[j] == dvars[j] for j in range(m))
        if vis != alld:
            fail("invisibility mismatch t=%d m=%d u=%s" % (t, m, u))
        good += not vis
    theta = 1 - good / len(Us)
    if abs(theta - 3.0 ** (-m)) > 1e-12:
        fail("theta=%g != 3^-m" % theta)
    formula = (1 - 2 * eps) ** len(T) * (good / len(Us))
    idx = {y: i for i, y in enumerate(SAT)}
    Ti = [idx[y] for y in T]
    si = idx[sig]
    n = 60000 if t < 3 else 15000
    acc = acc0 = dis = degen = 0
    fdom = list(itertools.product((1, -1), repeat=t))
    for _ in range(n):
        u = random.choice(Us)
        f = {z: random.choice((1, -1)) for z in fdom}
        g = [random.choice((1, -1)) for _ in SAT]
        mu = [(-1 if random.random() < eps else 1) for _ in SAT]
        h = [f[proj(y, u)] * g[i] * mu[i] for i, y in enumerate(SAT)]
        A = f[proj(sig, u)]
        Bg = math.prod(g[i] for i in Ti)
        Bh = math.prod(h[i] for i in Ti)
        acc += A * Bg * Bh
        acc0 += A * g[si] * h[si]
        dis += (Bg != g[si])
        degen += (h == g) or all(a == -c for a, c in zip(h, g))
    est, est0 = acc / n, acc0 / n
    tol = 5 / math.sqrt(n)
    if abs(est - formula) > tol:
        fail("bias t=%d m=%d est=%.4f formula=%.4f" % (t, m, est, formula))
    if abs(est0 - (1 - 2 * eps)) > tol:
        fail("honest bias est=%.4f" % est0)
    if abs(dis / n - 0.5) > tol:
        fail("distance fraction %.4f" % (dis / n))
    if degen / n > 2 ** (1 - 2 ** t) + tol:
        fail("degenerate rate %.4f" % (degen / n))
    deficit = ((1 - 2 * eps) - formula) / 2
    bound = 2 ** m * eps + 3.0 ** (-m) / 2
    if deficit > bound + 1e-12:
        fail("deficit %.4f > bound %.4f" % (deficit, bound))
    print("t=%d m=%d |T|=%d theta=%.4f bias MC=%.4f formula=%.4f "
          "deficit=%.4f<=%.4f dist=%.3f degen=%.4f"
          % (t, m, len(T), theta, est, formula, deficit, bound, dis / n, degen / n))


def check_parameters():
    gp = 0.105
    m = math.ceil(math.log(2 / gp, 3))
    eps = gp * 2 ** (-m - 2)
    Delta = 2 ** m * eps + 3.0 ** (-m) / 2
    print("gamma'=%.3f m=%d eps_max=%.5f Delta<=%.5f (need <= %.5f)"
          % (gp, m, eps, Delta, gp / 2))
    if not (m == 3 and Delta <= gp / 2 + 1e-15):
        fail("parameter arithmetic")
    for r0 in range(1, 12):
        k = 2 ** (r0 + 1) + 1
        N = 2 ** r0 + 1
        zeta = 0.5
        qlo = 1 / (4 * k * (1 - zeta / 2))
        qhi = qlo + 1 / (6 * k)
        if not (qhi <= 1 / (2 * k) + 1e-15
                and qhi * Delta <= gp / (4 * k) + 1e-15
                and (N - 1) * qhi < 0.25 and qlo < 0.25
                and abs((2 / 3) * (1 - zeta / 2) * qlo - 1 / (6 * k)) < 1e-15):
            fail("mass/distance arithmetic r0=%d" % r0)


if __name__ == "__main__":
    for t, m in [(1, 1), (2, 1), (2, 2), (3, 2), (3, 3)]:
        check_block(t, m)
    check_parameters()
    print("ALL OK" if ok else "SOME CHECKS FAILED")
    sys.exit(0 if ok else 1)
