"""Monte Carlo check of taus on B_5 at real p (exercises interior rungs)."""
import numpy as np
from check_bruteforce import ball
from ladder_connectivity import taus

R, p, N = 5, 0.55, 40000
V, E = ball(R)
idx = {v: j for j, v in enumerate(V)}
ea = np.array([idx[a] for a, _ in E])
ec = np.array([idx[c] for _, c in E])
tg = {(len(u), i): idx[(u, i)] for (u, i) in V if all(c == 0 for c in u)}
rng = np.random.default_rng(1)
hits = {t: 0 for t in tg}
for _ in range(N):
    op = rng.random(len(E)) < p
    par = list(range(len(V)))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for a, c in zip(ea[op], ec[op]):
        ra, rc = f(a), f(c)
        if ra != rc:
            par[ra] = rc
    r0 = f(idx[((), 0)])
    for t, j in tg.items():
        hits[t] += f(j) == r0
t = taus(np.array([p + 0j]), R, R)
for (k, i) in sorted(tg):
    mc = hits[(k, i)] / N
    ex = t[k][i][0].real
    sd = np.sqrt(ex * (1 - ex) / N + 1e-12)
    print(f"k={k} i={i} mc={mc:.4f} exact={ex:.4f} zscore={(mc-ex)/sd:+.2f}")
