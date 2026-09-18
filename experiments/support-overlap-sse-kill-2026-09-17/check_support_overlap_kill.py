#!/usr/bin/env python3
"""Replay checks for support-overlap-graphs-cannot-be-sse-no-instances.

Graphs: Grassmann G_2(6,3) (edges: 3-dim subspaces meeting in a 2-dim
subspace, the KMS 2-to-2 adjacency) and Johnson J(24,3) (edges: 3-sets
meeting in 2 points).  Support map psi(v) = nonzero vectors (resp. points).
Checks, for several p:
  (1) E_X A_X >= theta * E_X B_X exactly (A = E(Z_X,Z_X), B = mu(Z_X));
  (2) p b (1-p)^(b-1) <= m(p), and the Efron-Stein bound Var B_X <= rho_max m(p)
      (Monte Carlo, slack factor 2 for sampling error);
  (3) a random search over p-biased X with m(p) = 3 delta finds X with
      mu(Z_X) in [delta, 10 delta] and 1 - Phi(Z_X) >= theta - rho_max/delta;
  (4) the downsampling step: a random subset T of Z_X of size delta N has
      1 - Phi(T) >= (1 - Phi(Z_X)) (s-1)/|Z_X| on average (exact formula).
Run: python3 check_support_overlap_kill.py   (stdlib only)
"""
import itertools
import random


def grassmann(n, l):
    subs = set()
    for basis in itertools.combinations(range(1, 2 ** n), l):
        span = {0}
        for b in basis:
            span |= {s ^ b for s in span}
        if len(span) == 2 ** l:
            subs.add(frozenset(span - {0}))
    V = sorted(subs, key=sorted)
    need = 2 ** (l - 1) - 1
    adj = [[] for _ in V]
    for i in range(len(V)):
        for j in range(i + 1, len(V)):
            if len(V[i] & V[j]) == need:
                adj[i].append(j)
                adj[j].append(i)
    return V, adj, list(range(1, 2 ** n))


def johnson(n, k):
    V = [frozenset(c) for c in itertools.combinations(range(n), k)]
    idx = {v: i for i, v in enumerate(V)}
    adj = [[] for _ in V]
    for i, v in enumerate(V):
        for a in v:
            for c in range(n):
                if c not in v:
                    adj[i].append(idx[(v - {a}) | {c}])
    return V, adj, list(range(n))


def analyse(name, V, adj, U, deltas, trials=400, seed=1):
    rnd = random.Random(seed)
    N = len(V)
    d = len(adj[0])
    b = len(V[0])
    assert all(len(a) == d for a in adj)
    theta = min(len(V[i] & V[j]) / b for i in range(N) for j in adj[i])
    rho = max(sum(1 for v in V if x in v) for x in U) / N
    print(f"{name}: N={N} d={d} |psi|={b} theta={theta:.4f} rho_max={rho:.5f}")
    for p in [0.01, 0.05, 0.1, 0.2, 0.4]:
        q = 1 - p
        EB = 1 - q ** b
        EA = 0.0
        for i in range(N):
            for j in adj[i]:
                EA += 1 - 2 * q ** b + q ** len(V[i] | V[j])
        EA /= N * d
        assert EA >= theta * EB - 1e-12, (p, EA, EB)
        assert p * b * q ** (b - 1) <= EB + 1e-12
        # exact variance: Var B = N^-2 sum_{v,w} (q^|psi_v u psi_w| - q^(2b))
        var = 0.0
        for i in range(0, N, 1):
            vi = V[i]
            for j in range(N):
                var += q ** len(vi | V[j]) - q ** (2 * b)
        var /= N * N
        es = (1 - p) * rho * p * b * q ** (b - 1)
        print(f"  p={p}: E[A]={EA:.4f} >= theta E[B]={theta * EB:.4f}; "
              f"Var={var:.2e} <= ES bound {es:.2e} <= rho*m={rho * EB:.2e}")
        assert var <= es + 1e-12 and es <= rho * EB + 1e-12
    for delta in deltas:
        bound = theta - rho / delta
        lo, hi = 0.0, 1.0
        for _ in range(60):
            mid = (lo + hi) / 2
            if 1 - (1 - mid) ** b < 3 * delta:
                lo = mid
            else:
                hi = mid
        p = lo
        best = None
        for _ in range(trials):
            X = {x for x in U if rnd.random() < p}
            Z = [i for i, v in enumerate(V) if v & X]
            mu = len(Z) / N
            if not (delta <= mu <= 10 * delta):
                continue
            Zs = set(Z)
            e_in = sum(1 for i in Z for j in adj[i] if j in Zs)
            inside = e_in / (len(Z) * d)
            if best is None or inside > best[0]:
                best = (inside, len(Z), e_in)
            if inside >= bound:
                break
        assert best is not None and best[0] >= bound
        inside, S, e_in = best
        s = int(delta * N)
        # exact expectation for a uniform s-subset T of Z (no loops here)
        exp_in_T = e_in * s * (s - 1) / (S * (S - 1)) / (s * d)
        assert exp_in_T >= inside * (s - 1) / S - 1e-12
        print(f"  delta={delta}: bound theta-rho/delta={bound:.4f}; found 1-Phi={inside:.4f} "
              f"(mu={S / N:.3f}); downsampled E[1-Phi(T)]={exp_in_T:.4f}")


analyse("Grassmann G2(6,3)", *grassmann(6, 3), deltas=[0.25, 0.3])
analyse("Johnson J(24,3)", *johnson(24, 3), deltas=[0.2, 0.3])
print("all checks passed")
