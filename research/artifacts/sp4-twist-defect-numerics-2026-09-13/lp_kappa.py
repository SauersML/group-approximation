"""Exact constant kappa* for the abelian (coboundary) bar of Sp4(Z) twisted sectors, with an exact rational certificate.

kappa* = min_psi max_r |<e_r, psi> - k_r| over the distinct (exponent vector, lift) rows of pres6.json (all loops of
length <= 13 in the eight root generators).  With phases phi = 2 pi delta psi, an exact seed of class (-1)^k
(metaplectic) or 1 (trivial) rescaled into the theta-sector has maximal relator defect 2 sin(pi delta kappa*) whenever
delta kappa* <= 1/2, where delta = theta - 1/2 or theta.  So bar(theta) <= 2 sin(pi dist(theta, (1/2)Z) kappa*).
NUMERICS / FINITE LP: an upper bound on relator defects over a finite relator window; never a lower bound on sector
defects and never evidence of non-hyperlinearity.

Method: cutting-plane LP on a growing active set (memory-safe), then a rational rounding of psi checked exactly over
all rows, and a rational dual certificate (w_r >= 0, sum w_r = 1, sum w_r s_r e_r = 0) giving the matching lower bound
sum w_r s_r k_r on the LP value.
Usage: python3 lp_kappa.py pres6.json"""
import json, sys, itertools
import numpy as np
from fractions import Fraction
from scipy.optimize import linprog

pres = json.load(open(sys.argv[1]))
rels, lifts = pres["relators"], pres["lifts"]
rows = {}
for r, k in zip(rels, lifts):
    e = [0] * 8
    for x in r:
        e[x % 8] += 1 if x < 8 else -1
    rows[tuple(e) + (int(k),)] = 1
del pres, rels, lifts
U = np.array(sorted(rows), dtype=np.int64)
E, K = U[:, :8].astype(float), U[:, 8].astype(float)
n = len(K)
print(f"distinct rows {n}; lifts {sorted(set(K.astype(int).tolist()))}", flush=True)

def solve_subset(idx):
    Es, Ks = E[idx], K[idx]; m = len(idx)
    c = np.zeros(9); c[8] = 1.0
    A = np.vstack([np.hstack([Es, -np.ones((m, 1))]), np.hstack([-Es, -np.ones((m, 1))])])
    b = np.concatenate([Ks, -Ks])
    last = None
    for method in ("highs", "interior-point", "simplex"):
        try:
            res = linprog(c, A_ub=A, b_ub=b, bounds=[(None, None)] * 8 + [(0, None)], method=method)
            if res.status == 0:
                return res.x, method
            last = res.message
        except Exception as ex:
            last = repr(ex)
    raise RuntimeError(f"LP failed: {last}")

# start: all lifted rows plus rows of largest |k - 0| and a random sample
rng = np.random.default_rng(0)
idx = sorted(set(np.flatnonzero(K != 0).tolist()) | set(rng.choice(n, size=min(400, n), replace=False).tolist()))
for it in range(60):
    x, method = solve_subset(np.array(idx))
    psi, t = x[:8], x[8]
    resid = np.abs(E @ psi - K)
    viol = np.flatnonzero(resid > t + 1e-9)
    print(f"iter {it}: |active| {len(idx)} method {method} t {t:.10f} max over all rows {resid.max():.10f} violated {len(viol)}", flush=True)
    if len(viol) == 0:
        break
    add = viol[np.argsort(-resid[viol])][:200]
    idx = sorted(set(idx) | set(add.tolist()))
kappa = float(resid.max())
print(f"kappa* (float) = {kappa:.12f}", flush=True)

# exact rational upper bound: round psi, evaluate over ALL rows exactly
Er = [list(map(int, u[:8])) for u in U]; Kr = [int(u[8]) for u in U]
best_up = None
for den in (12, 24, 34, 48, 60, 68, 120, 136, 240, 340, 1000, 3400):
    q = [Fraction(v).limit_denominator(den) for v in psi]
    val = max(abs(sum(a * b for a, b in zip(e, q)) - k) for e, k in zip(Er, Kr))
    if best_up is None or val < best_up[0]:
        best_up = (val, q)
up, qpsi = best_up
print(f"exact rational upper bound: max_r |<e_r,psi_q> - k_r| = {up} = {float(up):.12f}, psi_q = {[str(v) for v in qpsi]}", flush=True)

# dual certificate on the active rows at the float optimum
act = np.flatnonzero(resid > kappa - 1e-7)
signs = np.sign(E[act] @ psi - K[act]); signs[signs == 0] = 1
print(f"active rows at optimum: {len(act)}", flush=True)
# find w >= 0 with sum w = 1 and sum w s e = 0; solve LP feasibility (small)
M = (signs[:, None] * E[act]).T
Aeq = np.vstack([M, np.ones((1, len(act)))]); beq = np.concatenate([np.zeros(8), [1.0]])
lb_float = None
for method in ("highs", "interior-point", "simplex"):
    try:
        rd = linprog(-(signs * K[act]) * -1.0, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * len(act), method=method)
        if rd.status == 0:
            w = rd.x; lb_float = float(-(signs * K[act]) @ w * -1.0); break
    except Exception as ex:
        print("dual method", method, "failed:", ex, flush=True)
if lb_float is not None:
    # lower bound for minimax: sum w_r s_r (e_r psi - k_r) <= max |.|, and sum w s e = 0 gives -sum w s k
    lbv = float(-(signs * K[act]) @ w)
    print(f"dual float: sum w s e = {np.abs(M @ w).max():.2e}, lower bound -sum w s k = {lbv:.12f}", flush=True)
    supp = np.flatnonzero(w > 1e-9)
    # exact rational solve on the support: least squares -> rational rounding -> exact check
    for den in (12, 24, 34, 60, 68, 120, 136, 340, 1000):
        wq = [Fraction(v).limit_denominator(den) for v in w[supp]]
        if any(v < 0 for v in wq):
            continue
        s = sum(wq)
        if s == 0:
            continue
        wq = [v / s for v in wq]
        bal = [sum(wq[j] * int(signs[supp[j]]) * Er[act[supp[j]]][i] for j in range(len(supp))) for i in range(8)]
        if all(v == 0 for v in bal):
            lbq = -sum(wq[j] * int(signs[supp[j]]) * Kr[act[supp[j]]] for j in range(len(supp)))
            print(f"exact dual certificate: support {len(supp)} rows, weights denominators <= {den}, lower bound {lbq} = {float(lbq):.12f}", flush=True)
            print("certificate rows (sign, exponent vector, lift, weight):", flush=True)
            for j in range(len(supp)):
                print(f"  {int(signs[supp[j]]):+d} {Er[act[supp[j]]]} {Kr[act[supp[j]]]} {wq[j]}", flush=True)
            if lbq == up:
                print(f"KAPPA* EXACT = {up}", flush=True)
            break
    else:
        print("no exact rational dual certificate found at tested denominators", flush=True)
for delta in (Fraction(1, 2), Fraction(1, 3), Fraction(1, 4), Fraction(1, 6), Fraction(1, 10)):
    print(f"delta {delta}: 2 sin(pi delta kappa*) = {2*np.sin(np.pi*float(delta)*float(up)):.6f}", flush=True)
print("DONE", flush=True)
