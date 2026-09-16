"""Test (J): for a finitely supported probability measure mu on vertices of a
RAAG Salvetti cover, is there a point b of the l^1 cube complex with
d(x,b) <= int d(x,y) dmu(y) for all vertices x?  By the gate property it is
enough to search b in the convex hull K of supp(mu) and check x in K."""
import sys, random, itertools
import numpy as np
from scipy.optimize import linprog
from raagcube import RAAG, ball, hull_fast, Complex

def jensen_feasible(K, mu, return_point=False):
    n = len(K.V)
    coords = K.coord
    F = np.zeros(n)
    for y, w in mu.items():
        cy = coords[y]
        for i in range(n):
            F[i] += w * bin(coords[i] ^ cy).count("1")
    best = None
    for (f, m) in K.cubes():
        free = [h for h in range(K.nh) if (m >> h) & 1]
        k = len(free)
        A = np.zeros((n, k))
        rhs = np.zeros(n)
        for i in range(n):
            cx = coords[i]
            const = bin((cx ^ f) & ~m).count("1")
            for j, h in enumerate(free):
                if (cx >> h) & 1:
                    const += 1
                    A[i, j] = -1.0
                else:
                    A[i, j] = 1.0
            rhs[i] = F[i] - const
        # minimize slack t: A b - t <= rhs, t free; feasible iff t* <= 0
        Aub = np.hstack([A, -np.ones((n, 1))])
        c = np.zeros(k + 1); c[-1] = 1.0
        bounds = [(0, 1)] * k + [(None, None)]
        res = linprog(c, A_ub=Aub, b_ub=rhs, bounds=bounds, method="highs")
        if res.status == 0:
            t = res.x[-1]
            if best is None or t < best[0]:
                best = (t, f, m, res.x[:-1])
            if t <= 1e-9 and not return_point:
                return True, best
    return (best is not None and best[0] <= 1e-9), best

def run(G, name, R, trials, maxsupp, rng):
    B = sorted(ball(G, R))
    worst = None
    for tr in range(trials):
        p = rng.randint(2, maxsupp)
        S = rng.sample(B, p)
        K = Complex(G, hull_fast(G, S))
        assert K.check_isometric(100, rng)
        idx = [K.idx[s] for s in S]
        if rng.random() < 0.5:
            mu = {i: 1.0 / p for i in idx}
        else:
            ws = [rng.randint(1, 5) for _ in idx]
            tot = sum(ws)
            mu = {i: w / tot for i, w in zip(idx, ws)}
        ok, best = jensen_feasible(K, mu)
        if worst is None or best[0] > worst[0]:
            worst = (best[0], S, mu)
        if not ok:
            print(name, "FAIL", "slack", best[0], "support", S, "weights", list(mu.values()), "hull size", len(K.V))
            sys.stdout.flush()
    print(name, "done", trials, "trials; worst min-slack", worst[0])

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    P4 = RAAG(4, [(0, 1), (1, 2), (2, 3)])
    run(P4, "P4", 3, 60, 4, rng)
    # cone on P4: z=4
    CP4 = RAAG(5, [(0, 1), (1, 2), (2, 3), (4, 0), (4, 1), (4, 2), (4, 3)])
    run(CP4, "K1*P4", 2, 40, 4, rng)
