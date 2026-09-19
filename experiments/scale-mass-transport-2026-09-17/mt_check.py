#!/usr/bin/env python3
"""Checks for finite-scale-compressors-preserve-kazhdan-fixed-algebras.

Finite model: a finite set Y, a partition into clusters Q_i, and a permutation u
of Y. pi(i) is the dominant target of cluster i, ell(i) the loss, L = sum ell.
A cluster is good if ell(i) <= theta |Q_i|. The bad set B is the points of bad
clusters together with the points y of good clusters with u y outside Q_pi(i).
phi(y) = log |Q(y)|, and J_eta is the set of y outside B with
phi(u y) >= phi(y) + eta.

Checks:
 1. the windowed mass-transport inequality (Lemma MT)
        eta |J_eta cap phi^-1[a, b - eta]| <= (b - a)|B| + sum_(y not in B) kappa(y)
    with kappa(y) = -log(1 - ell(i)/|Q_i|) <= 2 ell(i)/|Q_i|, on random instances;
 2. the fixed-algebra bound ||g o u^-1 - h||_1 <= 2 ||g||_oo (|B| + |J_eta|) with the
    tight-cluster function h, on random instances;
 3. the doubling tower: lambda -> 0 but lambda log N -> log 2, w(J_eta) -> 1, and
    Ad(u) moves a random sign function g in D(Q) a definite distance from D(Q);
 4. the long drifting cycle with bounded cluster sizes: unbounded period (BP fails),
    one window of bounded length (FS holds), and Ad(u) preserves D(Q) up to o(1).
"""
import math
import random


def dominant(clusters, cl_of, u):
    """Dominant targets and losses of a permutation u on a partition."""
    pi, ell = [], []
    for Q in clusters:
        cnt = {}
        for y in Q:
            j = cl_of[u[y]]
            cnt[j] = cnt.get(j, 0) + 1
        j, c = max(cnt.items(), key=lambda kv: (kv[1], -kv[0]))
        pi.append(j)
        ell.append(len(Q) - c)
    return pi, ell


def analyse(clusters, u, theta, eta):
    N = sum(len(Q) for Q in clusters)
    cl_of = [0] * N
    for i, Q in enumerate(clusters):
        for y in Q:
            cl_of[y] = i
    pi, ell = dominant(clusters, cl_of, u)
    L = sum(ell)
    phi = [math.log(len(clusters[cl_of[y]])) for y in range(N)]
    good_cl = [ell[i] <= theta * len(Q) for i, Q in enumerate(clusters)]
    bad = [not (good_cl[cl_of[y]] and cl_of[u[y]] == pi[cl_of[y]]) for y in range(N)]
    kappa = [0.0] * N
    for y in range(N):
        if not bad[y]:
            i = cl_of[y]
            kappa[y] = -math.log(1 - ell[i] / len(clusters[i]))
    J = [(not bad[y]) and phi[u[y]] >= phi[y] + eta - 1e-12 for y in range(N)]
    return dict(N=N, cl_of=cl_of, pi=pi, ell=ell, L=L, phi=phi, bad=bad,
                kappa=kappa, J=J, good_cl=good_cl)


def check_window(A, u, a, b, eta):
    """Return (lhs, rhs) of Lemma MT on the window [a, b]."""
    N, phi, bad, J, kappa = A["N"], A["phi"], A["bad"], A["J"], A["kappa"]
    cnt = sum(1 for y in range(N) if J[y] and a <= phi[y] <= b - eta)
    lhs = eta * cnt
    rhs = (b - a) * sum(bad) + sum(kappa[y] for y in range(N) if not bad[y])
    return lhs, rhs


def fixed_algebra_error(clusters, u, A, g, theta, eta):
    """||g o u^-1 - h||_1 for the tight-cluster function h, and the bound."""
    N, cl_of, pi = A["N"], A["cl_of"], A["pi"]
    tight = {}
    for i, Q in enumerate(clusters):
        if A["good_cl"][i] and len(clusters[pi[i]]) < math.exp(eta) * len(Q):
            assert pi[i] not in tight, "two tight preimages of one cluster"
            tight[pi[i]] = i
    uinv = [0] * N
    for y in range(N):
        uinv[u[y]] = y
    err = 0.0
    for yp in range(N):
        j = cl_of[yp]
        h = g[clusters[tight[j]][0]] if j in tight else 0.0
        err += abs(g[uinv[yp]] - h)
    bound = 2 * max(abs(x) for x in g) * (sum(A["bad"]) + sum(A["J"]))
    return err, bound


def dist_to_D(clusters, u, g):
    """L1 distance of g o u^-1 from the cluster-constant functions, g = +-1."""
    N = len(g)
    uinv = [0] * N
    for y in range(N):
        uinv[u[y]] = y
    d = 0
    for Q in clusters:
        plus = sum(1 for yp in Q if g[uinv[yp]] > 0)
        d += 2 * min(plus, len(Q) - plus)
    return d


def random_instance(rng, nclusters, maxexp, swaps):
    sizes = [2 ** rng.randint(0, maxexp) for _ in range(nclusters)]
    clusters, pos = [], 0
    for s in sizes:
        clusters.append(list(range(pos, pos + s)))
        pos += s
    N = pos
    order = list(range(nclusters))
    rng.shuffle(order)
    seq = [y for i in order for y in clusters[i]]
    shift = rng.randint(0, N - 1)
    u = [0] * N
    for p, y in enumerate(seq):
        u[y] = seq[(p + shift) % N]
    for _ in range(swaps):
        a, b = rng.randrange(N), rng.randrange(N)
        u[a], u[b] = u[b], u[a]
    return clusters, u


def tower(k):
    clusters, level_ids, pos = [], [], 0
    for m in range(k + 1):
        ids = []
        for _ in range(2 ** (k - m)):
            clusters.append(list(range(pos, pos + 2 ** m)))
            ids.append(len(clusters) - 1)
            pos += 2 ** m
        level_ids.append(ids)
    N = pos
    u = [None] * N
    for m in range(k):
        for c, tgt in enumerate(level_ids[m + 1]):
            T = clusters[tgt]
            A, B = clusters[level_ids[m][2 * c]], clusters[level_ids[m][2 * c + 1]]
            for t, y in enumerate(A + B):
                u[y] = T[t]
    top = clusters[level_ids[k][0]]
    singles = [clusters[i][0] for i in level_ids[0]]
    for y, z in zip(top, singles):
        u[y] = z
    assert sorted(u) == list(range(N))
    return clusters, u


def drift_cycle(C, M):
    sizes = [int(round(M * (0.75 + 0.25 * math.sin(2 * math.pi * c / C)))) for c in range(C)]
    clusters, pos = [], 0
    for s in sizes:
        clusters.append(list(range(pos, pos + s)))
        pos += s
    N = pos
    u = [None] * N
    spare_src, spare_tgt = [], []
    for c in range(C):
        A, T = clusters[c], clusters[(c + 1) % C]
        m = min(len(A), len(T))
        for t in range(m):
            u[A[t]] = T[t]
        spare_src += A[m:]
        spare_tgt += T[m:]
    assert len(spare_src) == len(spare_tgt)
    for y, z in zip(spare_src, spare_tgt):
        u[y] = z
    assert sorted(u) == list(range(N))
    return clusters, u


def period_mass(A, clusters, p):
    """Weight of clusters on pi-cycles of length <= p."""
    pi, tot = A["pi"], 0
    for i, Q in enumerate(clusters):
        j = i
        for _ in range(p):
            j = pi[j]
            if j == i:
                tot += len(Q)
                break
    return tot / A["N"]


def main():
    rng = random.Random(20260917)
    theta, eta = 0.125, 0.125
    assert (1 - theta) * math.exp(-eta) > 0.5
    worst = 0.0
    for trial in range(300):
        clusters, u = random_instance(rng, rng.randint(5, 60), rng.randint(0, 7),
                                      rng.randint(0, 40))
        A = analyse(clusters, u, theta, eta)
        top = max(A["phi"])
        for (a, b) in [(0.0, top + eta), (0.0, 1.5), (1.0, 3.0), (2.0, top + eta)]:
            if b <= a + eta:
                continue
            lhs, rhs = check_window(A, u, a, b, eta)
            assert lhs <= rhs + 1e-9, (trial, a, b, lhs, rhs)
            if rhs > 0:
                worst = max(worst, lhs / rhs)
        assert sum(A["kappa"][y] for y in range(A["N"]) if not A["bad"][y]) <= 2 * A["L"] + 1e-9
        assert sum(A["bad"]) <= (1 + 1 / theta) * A["L"] + 1e-9
        g = [rng.choice([-1.0, 1.0]) for _ in range(len(clusters))]
        gy = [g[A["cl_of"][y]] for y in range(A["N"])]
        err, bound = fixed_algebra_error(clusters, u, A, gy, theta, eta)
        assert err <= bound + 1e-9, (trial, err, bound)
    print("random instances: Lemma MT, |B| and kappa bounds, fixed-algebra bound all hold "
          "(300 trials); max lhs/rhs = %.3f" % worst)

    print("\ndoubling tower (no scale hypothesis): loss -> 0 but Ad(u) leaves D(Q)")
    print(" k      N   lambda  lambda*logN  w(J_eta)  dist(Ad u g, D)/N")
    for k in [4, 6, 8, 10, 12, 14]:
        clusters, u = tower(k)
        A = analyse(clusters, u, theta, eta)
        N = A["N"]
        gy = [0.0] * N
        for Q in clusters:
            s = rng.choice([-1.0, 1.0])
            for y in Q:
                gy[y] = s
        d = dist_to_D(clusters, u, gy)
        lam = A["L"] / N
        print("%2d %7d  %.4f   %.4f     %.4f    %.4f" %
              (k, N, lam, lam * math.log(N), sum(A["J"]) / N, d / N))

    print("\nlong drifting cycle, bounded sizes (FS holds, BP fails): Ad(u) keeps D(Q)")
    print("   C    M      N   lambda  BP_10-mass  w(J_eta)  dist(Ad u g, D)/N")
    for C, M in [(20, 40), (80, 40), (320, 40), (1280, 40)]:
        clusters, u = drift_cycle(C, M)
        A = analyse(clusters, u, theta, eta)
        N = A["N"]
        gy = [0.0] * N
        for Q in clusters:
            s = rng.choice([-1.0, 1.0])
            for y in Q:
                gy[y] = s
        d = dist_to_D(clusters, u, gy)
        print("%4d %4d %6d  %.4f    %.4f     %.4f    %.4f" %
              (C, M, N, A["L"] / N, period_mass(A, clusters, 10), sum(A["J"]) / N, d / N))


if __name__ == "__main__":
    main()
