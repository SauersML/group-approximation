"""Exact-rational adversary upper bound on R*(k) from folded columns.

Runs the folded column generation of hadk_colgen.run_F (starting from edge-orbit weights W
given on the command line, e.g. the dual gadget of the unfolded phase), then certifies:

  * each column is a folded f with f(chi_a) = xi_a at its pattern representative
    (re-checked here), stored as integer cut counts per edge orbit;
  * the LP mixture p is rounded to rationals and renormalized inside each pattern orbit so
    that sum_{c in q} p_c = |orbit q| / 2^|P| exactly; the group-symmetrized mixture is then
    a folded distribution random on P (orbit-stabilizer);
  * UB = K * max_o sum_c p_c cutcount_c(o) / |o|, in exact arithmetic.

usage: python3 hadk_fold_ub.py k W0,W1,... [rounds]
"""
import sys, time
from fractions import Fraction
import numpy as np
from hadk_setup import setup
from hadk_mincut import unfolded_price
from hadk_fold import local_search, pinned, full_f
from hadk_colgen import master, orbavg, caps_from

k = int(sys.argv[1])
W = np.array([int(t) for t in sys.argv[2].split(",")], dtype=np.float64)
rounds = int(sys.argv[3]) if len(sys.argv) > 3 else 300
t0 = time.time()
S = setup(k)
K, half = S["K"], S["N"] >> 1
rng = np.random.default_rng(0)
cols, cnts, fs = [], [], []


def add_cols(lam, nu=None, restarts=4):
    wE, cap = caps_from(S, lam)
    n = 0
    for q, xi in enumerate(S["reps"]):
        _, _, f0 = unfolded_price(S, cap, xi)
        best = None
        mirror = ~f0[S["full"] ^ np.arange(half)]          # rep value of x -> -f0(-x)
        for b0 in [f0[:half].copy(), mirror] + [rng.random(half) < 0.5 for _ in range(restarts)]:
            v, cut, b = local_search(S, wE, xi, b0, rng=rng)
            if best is None or v < best[0]:
                best = (v, cut, b)
        if nu is None or best[0] < nu[q] - 1e-9:
            b = best[2]
            for r, val in pinned(S, xi).items():
                assert b[r] == val
            cols.append((q, orbavg(S, best[1])))
            cnts.append(np.bincount(S["orb"], weights=best[1].astype(np.int64), minlength=S["norb"]).astype(np.int64))
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
# exact certificate
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
      f"R*({k}) <= {K * worst} ~ {float(K * worst):.6f}")
