#!/usr/bin/env python3
"""Calibration of fpbs-expander-approximant-giant-data-is-glued on random 3-regular graphs.

Random 3-regular multigraphs (configuration model, loops discarded) are large-set
expanders converging locally to the 3-regular tree T_3, where p_c = 1/2 and p_u = 1.
For bond percolation at level p we measure
  c1, c2   = |C_1|/n, |C_2|/n                (theorem part A: c2 -> 0 for every p)
  glued    = (1/n) sum_x sum_{y~x} 1{x <-> y}  (part B: -> 3[p + (1-p) eta^2])
  local    = 3p = sum_{y~o} P_T(o <-> y)       (the ungluded two-point sum on the tree)
  s_R      = (1/n) sum_x sum_{y~x} 1{xy closed, x <-> y, not connected inside B_R(x)}
                                              (part D: -> 3(1-p) eta^2 as n -> inf, R -> inf)
where eta = P(a fixed half-tree branch percolates) solves eta = 1-(1-p eta)^2, and
zeta = 1-(1-p eta)^3.  Usage: python3 rrg_glued_calibration.py [n] [R] [seed]
"""
import random
import sys
from collections import deque


def rrg(n, rng):
    stubs = [v for v in range(n) for _ in range(3)]
    rng.shuffle(stubs)
    edges = []
    for i in range(0, len(stubs) - 1, 2):
        a, b = stubs[i], stubs[i + 1]
        if a != b:
            edges.append((a, b))
    return edges


def find(par, x):
    while par[x] != x:
        par[x] = par[par[x]]
        x = par[x]
    return x


def eta_of(p):
    e = 1.0
    for _ in range(20000):
        e = 1 - (1 - p * e) ** 2
    return e


def run(n, R, p, edges, rng):
    open_ = [rng.random() < p for _ in edges]
    adj = [[] for _ in range(n)]  # graph adjacency (for balls)
    oadj = [[] for _ in range(n)]  # open adjacency
    par = list(range(n))
    for (a, b), o in zip(edges, open_):
        adj[a].append(b)
        adj[b].append(a)
        if o:
            oadj[a].append(b)
            oadj[b].append(a)
            ra, rb = find(par, a), find(par, b)
            if ra != rb:
                par[ra] = rb
    roots = [find(par, v) for v in range(n)]
    size = {}
    for r in roots:
        size[r] = size.get(r, 0) + 1
    sizes = sorted(size.values(), reverse=True) + [0, 0]
    big = max(size, key=size.get)
    same = 0
    srem = 0
    for (a, b), o in zip(edges, open_):
        if roots[a] != roots[b]:
            continue
        same += 1
        if o or roots[a] != big:
            continue
        # distances from a in the graph, truncated at R
        dist = {a: 0}
        dq = deque([a])
        while dq:
            u = dq.popleft()
            if dist[u] == R:
                continue
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1
                    dq.append(w)
        # open connection a -> b inside B_R(a)
        seen = {a}
        dq = deque([a])
        hit = False
        while dq and not hit:
            u = dq.popleft()
            for w in oadj[u]:
                if w in dist and w not in seen:
                    if w == b:
                        hit = True
                        break
                    seen.add(w)
                    dq.append(w)
        if not hit:
            srem += 1
    return sizes[0] / n, sizes[1] / n, 2 * same / n, 2 * srem / n


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = random.Random(seed)
    edges = rrg(n, rng)
    print(f"n={n} R={R} seed={seed} edges={len(edges)}")
    print("p     c1      zeta    c2      glued   pred    local3p s_R     pred_s")
    for p in (0.3, 0.45, 0.55, 0.7, 0.85):
        eta = eta_of(p) if p > 0.5 else 0.0
        zeta = 1 - (1 - p * eta) ** 3
        c1, c2, gl, sR = run(n, R, p, edges, rng)
        print(f"{p:.2f}  {c1:.4f}  {zeta:.4f}  {c2:.4f}  {gl:.4f}  {3*(p+(1-p)*eta*eta):.4f}  "
              f"{3*p:.4f}  {sR:.4f}  {3*(1-p)*eta*eta:.4f}")


if __name__ == "__main__":
    main()
