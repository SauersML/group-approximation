"""Column generation sandwich for R*(k) = K z*(Had_k) (k = 3 validation, k = 4 target).

Master LP (same as minimax_gadget_value.solve): adversary mixture over pattern-orbit reps,
symmetrized, minimize the max orbit-average cut probability z.

  mode U (lower side): columns are UNFOLDED min cuts (antipodal pins), exact via max flow.
     Converged value z_U <= z*.  Certificate: the dual gadget (integer orbit weights W);
     LB = sum_q Pr[q] mincut_W(q) / W(E) computed in exact integers, and K*LB <= R*(k).
  mode F (upper side): columns are FOLDED cuts from local search.  Any value is >= z*,
     so K*z_F >= R*(k) is a valid adversary bound (not exact pricing).

usage: python3 hadk_colgen.py k [rounds]
"""
import sys, time
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from hadk_setup import setup
from hadk_mincut import unfolded_price
from hadk_fold import local_search

SCALE = 10 ** 6


def master(S, cols):
    orb, norb = S["orb"], S["norb"]
    nq = len(S["reps"])
    M = len(cols)
    cvec = np.r_[np.zeros(M), 1.0]
    Aub = np.zeros((norb, M + 1)); Aub[:, M] = -1
    Aeq = np.zeros((nq, M + 1))
    for c, (q, a) in enumerate(cols):
        Aub[:, c] = a; Aeq[q, c] = 1
    beq = S["psize"] / S["npat"]
    res = linprog(cvec, A_ub=Aub, b_ub=np.zeros(norb), A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * M + [(None, None)], method="highs")
    return res.fun, -res.ineqlin.marginals, res.eqlin.marginals, res.x


def orbavg(S, cut):
    return np.bincount(S["orb"], weights=cut.astype(float), minlength=S["norb"]) / S["osize"]


def caps_from(S, lam):
    wE = lam[S["orb"]] / S["osize"][S["orb"]]
    return wE, np.rint(wE / wE.max() * SCALE).astype(np.int64)


def certify(S, W_orb):
    """exact lower bound from integer orbit weights W_orb (weight per edge in orbit o)."""
    cap = W_orb[S["orb"]].astype(np.int64)
    tot = int(cap.sum())
    num = Fraction(0)
    for q, xi in enumerate(S["reps"]):
        v, _, _ = unfolded_price(S, cap, xi)
        num += Fraction(int(S["psize"][q]), int(S["npat"])) * v
    return S["K"] * num / tot


def run_U(S, rounds=200, log=print):
    cols = []
    w0 = np.ones(S["E"], dtype=np.int64)
    for q, xi in enumerate(S["reps"]):
        cols.append((q, orbavg(S, unfolded_price(S, w0, xi)[1])))
    for it in range(rounds):
        z, lam, nu, _ = master(S, cols)
        wE, cap = caps_from(S, lam)
        added = 0
        for q, xi in enumerate(S["reps"]):
            _, cut, _ = unfolded_price(S, cap, xi)
            if float(cut @ wE) < nu[q] - 1e-9:
                cols.append((q, orbavg(S, cut))); added += 1
        log(f"U round {it}: K*z = {S['K'] * z:.6f}, added {added}")
        if added == 0:
            break
    return z, lam, cols


def run_F(S, rounds=200, restarts=4, seed=0, log=print, lam_init=None):
    rng = np.random.default_rng(seed)
    half = S["N"] >> 1
    cols = []
    lam = lam_init if lam_init is not None else np.ones(S["norb"]) / S["norb"]

    def folded_cols(lam, nu=None):
        wE, cap = caps_from(S, lam)
        out = []
        for q, xi in enumerate(S["reps"]):
            _, _, f0 = unfolded_price(S, cap, xi)
            best = None
            starts = [f0[:half].copy()] + [rng.random(half) < 0.5 for _ in range(restarts)]
            for b0 in starts:
                v, cut, _ = local_search(S, wE, xi, b0, rng=rng)
                if best is None or v < best[0]:
                    best = (v, cut)
            if nu is None or best[0] < nu[q] - 1e-9:
                out.append((q, orbavg(S, best[1])))
        return out
    cols += folded_cols(lam)
    for it in range(rounds):
        z, lam, nu, _ = master(S, cols)
        new = folded_cols(lam, nu)
        cols += new
        log(f"F round {it}: K*z = {S['K'] * z:.6f}, added {len(new)}")
        if not new:
            break
    return z, lam, cols


if __name__ == "__main__":
    k = int(sys.argv[1])
    rounds = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    t = time.time()
    S = setup(k)
    K = S["K"]
    print(f"k={k}: E={S['E']} orbits={S['norb']} sizes={S['osize'].tolist()} patterns={len(S['reps'])}", flush=True)
    lg = lambda s: print(s, f"[{time.time() - t:.0f}s]", flush=True)
    zU, lamU, _ = run_U(S, rounds, lg)
    W = np.rint(lamU / S["osize"] / (lamU / S["osize"]).max() * SCALE).astype(np.int64)
    LB = certify(S, W)
    print(f"unfolded relaxation K*z_U = {K * zU:.6f}")
    print(f"certified LB (exact, dual gadget integer weights) R*({k}) >= {LB} = {float(LB):.6f}")
    print("gadget orbit weights (per edge, scaled):", W.tolist())
    zF, lamF, _ = run_F(S, rounds, log=lg, lam_init=lamU)
    print(f"folded adversary UB R*({k}) <= K*z_F = {K * zF:.6f}")
    WF = np.rint(lamF / S["osize"] / max((lamF / S["osize"]).max(), 1e-300) * SCALE).astype(np.int64)
    if WF.sum() > 0:
        LBF = certify(S, WF)
        print(f"unfolded value of folded-master dual gadget: {LBF} = {float(LBF):.6f}")
    print(f"done [{time.time() - t:.0f}s]")
