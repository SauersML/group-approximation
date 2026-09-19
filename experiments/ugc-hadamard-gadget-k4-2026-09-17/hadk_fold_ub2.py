"""hadk_fold_ub.py with stronger heuristic pricing (certificate logic unchanged).

Extra local-search starts per pattern, taken from the folding-lemma construction:
f0 = unfolded min cut, f~(x) = -f0(-x), T = {f0 = f~ = +1}, D = {f0 != f~}.
The start is +1 on T, -1 on -T, and sigma * x_i on D, for `ndict` random (i, sigma).
Then `nkick` iterated-local-search kicks (flip a random 3% of free reps, re-descend).
Pricing stays heuristic; UB validity does not depend on it (every column is re-checked
folded + pinned, and the certificate is exact rational).

usage: python3 hadk_fold_ub2.py k W0,W1,... [rounds] [ndict] [nkick]
"""
import sys, time
from fractions import Fraction
import numpy as np
from hadk_setup import setup
from hadk_mincut import unfolded_price
from hadk_fold import local_search, pinned
from hadk_colgen import master, orbavg, caps_from

k = int(sys.argv[1])
W = np.array([int(t) for t in sys.argv[2].split(",")], dtype=np.float64)
rounds = int(sys.argv[3]) if len(sys.argv) > 3 else 300
ndict = int(sys.argv[4]) if len(sys.argv) > 4 else 6
nkick = int(sys.argv[5]) if len(sys.argv) > 5 else 4
t0 = time.time()
S = setup(k)
K, half, full = S["K"], S["N"] >> 1, S["full"]
rng = np.random.default_rng(1)
cols, cnts = [], []
reps = np.arange(half, dtype=np.int64)


def starts(f0):
    ft = ~f0[full ^ np.arange(S["N"])]            # f~(x) = -f0(-x)
    T, D = (f0 & ft)[:half], (f0 ^ ft)[:half]
    out = [f0[:half].copy(), ft[:half].copy()]
    for _ in range(ndict):
        i, sg = int(rng.integers(K)), bool(rng.integers(2))
        dic = (((reps >> i) & 1) == 0) ^ sg
        out.append(np.where(D, dic, T))
    out += [rng.random(half) < 0.5 for _ in range(2)]
    return out


def add_cols(lam, nu=None):
    wE, cap = caps_from(S, lam)
    n = 0
    for q, xi in enumerate(S["reps"]):
        _, _, f0 = unfolded_price(S, cap, xi)
        best = None
        for b0 in starts(f0):
            v, cut, b = local_search(S, wE, xi, b0, rng=rng)
            if best is None or v < best[0]:
                best = (v, cut, b)
        for _ in range(nkick):
            b0 = best[2].copy()
            fl = rng.random(half) < 0.03
            b0[fl] = ~b0[fl]
            v, cut, b = local_search(S, wE, xi, b0, rng=rng)
            if v < best[0]:
                best = (v, cut, b)
        if nu is None or best[0] < nu[q] - 1e-9:
            b = best[2]
            for r, val in pinned(S, xi).items():
                assert b[r] == val
            cols.append((q, orbavg(S, best[1])))
            cnts.append(np.bincount(S["orb"], weights=best[1].astype(np.int64),
                                    minlength=S["norb"]).astype(np.int64))
            n += 1
    return n


lam = W * S["osize"]
lam = lam / lam.sum()
add_cols(lam)
for it in range(rounds):
    z, lam, nu, x = master(S, cols)
    n = add_cols(lam, nu)
    print(f"F round {it}: K*z = {K * z:.6f}, added {n} [{time.time() - t0:.0f}s]", flush=True)
    if n == 0:
        break
z, lam, nu, x = master(S, cols)
print("final dual gadget (orbit weights x1e6):",
      ",".join(str(int(round(v))) for v in 1e6 * (lam / S["osize"]) / (lam / S["osize"]).max()))
p = [Fraction(max(float(v), 0.0)).limit_denominator(10 ** 9) for v in x[:-1]]
target = [Fraction(int(S["psize"][q]), int(S["npat"])) for q in range(len(S["reps"]))]
tot = [Fraction(0)] * len(S["reps"])
for c, (q, _) in enumerate(cols):
    tot[q] += p[c]
for c, (q, _) in enumerate(cols):
    p[c] = p[c] * target[q] / tot[q]
worst = Fraction(0)
for o in range(S["norb"]):
    val = sum((p[c] * int(cnts[c][o]) for c in range(len(cols)) if p[c]), Fraction(0)) / int(S["osize"][o])
    worst = max(worst, val)
print(f"float LP: R*({k}) <= {K * z:.6f}")
print(f"certified (exact rational mixture of {sum(1 for v in p if v)} folded columns): "
      f"R*({k}) <= {float(K * worst):.9f}")
print("exact:", K * worst)
