"""Brute-force check of ladder_connectivity.taus on the balls B_1, B_2 of
T_3 box K_2, at a complex parameter (polynomial identity check)."""
import itertools
import numpy as np
from ladder_connectivity import taus


def ball(R):
    # tree T_3 vertices as tuples; root ()
    verts = [()]
    frontier = [()]
    for d in range(R):
        nf = []
        for u in frontier:
            kids = range(3) if u == () else range(2)
            for c in kids:
                nf.append(u + (c,))
        verts += nf
        frontier = nf
    V = [(u, 0) for u in verts] + [(u, 1) for u in verts if len(u) <= R - 1]
    Vs = set(V)
    E = []
    for (u, i) in V:
        if len(u) >= 1 and (u[:-1], i) in Vs:
            E.append(((u[:-1], i), (u, i)))
        if i == 0 and (u, 1) in Vs:
            E.append(((u, 0), (u, 1)))
    return V, E


def brute(R, z):
    V, E = ball(R)
    idx = {v: j for j, v in enumerate(V)}
    targets = {}
    for (u, i) in V:
        if all(c == 0 for c in u):
            targets[(len(u), i)] = idx[(u, i)]
    acc = {t: 0j for t in targets}
    m = len(E)
    for mask in range(1 << m):
        par = list(range(len(V)))

        def f(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        cnt = 0
        for b in range(m):
            if mask >> b & 1:
                cnt += 1
                a, c = E[b]
                ra, rc = f(idx[a]), f(idx[c])
                if ra != rc:
                    par[ra] = rc
        w = z ** cnt * (1 - z) ** (m - cnt)
        r0 = f(idx[((), 0)])
        for t, j in targets.items():
            if f(j) == r0:
                acc[t] += w
    return acc, m


if __name__ == "__main__":
    z = np.array([0.37 + 0.21j])
    for R in (1, 2):
        acc, m = brute(R, z[0])
        t = taus(z, R, R)
        print("R", R, "edges", m)
        for (k, i), val in sorted(acc.items()):
            ours = t[k][i][0]
            print(f"  k={k} i={i} brute={val:.12f} transfer={ours:.12f}"
                  f" err={abs(val-ours):.2e}")
