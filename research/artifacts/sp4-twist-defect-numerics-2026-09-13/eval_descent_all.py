"""All-relator evaluation of mod-3 descent tuples (optimize7.py output, or seed JSON start points).

The product-order convention is chosen by a self-check: on the exact metaplectic seed seed_theta_d10.json one order
gives rho(r) = (-1)^{k_r} I on every relator to rounding.  For each tuple it reports, over ALL relators of
pres6.json, the maximal normalized-HS defect ||rho(r) - omega^{k_r} I||_{2,d} (unlifted and lifted), the mean square,
the number of relators above the exact abelian bar 2 sin(5 pi/102), the per-generator distance to the stacked
metaplectic seed after removing the best phase, and the pure coboundary defect carrying those phases.
NUMERICS: upper bounds on relator defects over the length-13 window only; never a lower bound, never evidence of a
sector floor, and never evidence for or against non-hyperlinearity.
Usage: python3 eval_descent_all.py pres6.json seed_theta_d10.json TUPLE [TUPLE ...]   (TUPLE = .npy or seed .json)"""
import json, sys, time
import numpy as np

BAR = 2*np.sin(5*np.pi/102)
OMEGA = np.exp(2j*np.pi/3)
pres = json.load(open(sys.argv[1]))
rels, lifts = pres["relators"], np.array(pres["lifts"], dtype=np.int64)
del pres
N = len(rels)
len_of = np.array([len(r) for r in rels])
bylen = {}
for i, r in enumerate(rels):
    bylen.setdefault(len(r), []).append(i)
classes = [(np.array(ii, dtype=np.int64), np.array([rels[i] for i in ii], dtype=np.int64)) for _, ii in sorted(bylen.items())]
E = np.zeros((N, 8))
for i, r in enumerate(rels):
    for x in r:
        E[i, x % 8] += 1 if x < 8 else -1
del rels
lifted = lifts != 0
sgn = (-1.0)**lifts
target = OMEGA**lifts

def load_tuple(fn):
    if fn.endswith(".npy"):
        U = np.load(fn)
    else:
        J = json.load(open(fn)); a = np.array(J["seed"], dtype=float)
        U = (a[:, :, 0] + 1j*a[:, :, 1]).reshape(8, J["d"], J["d"])
    return np.asarray(U, dtype=complex)

def traces(U, order):
    d = U.shape[1]
    G = np.concatenate([U, np.conj(np.transpose(U, (0, 2, 1)))], axis=0)
    chunk = max(2000, int(3e8 // (16*d*d)))
    tr = np.empty(N, dtype=complex)
    for idx, W in classes:
        for a in range(0, len(idx), chunk):
            Wc = W[a:a+chunk]
            P = G[Wc[:, 0]]
            for j in range(1, Wc.shape[1]):
                P = P @ G[Wc[:, j]] if order == "left" else G[Wc[:, j]] @ P
            tr[idx[a:a+chunk]] = np.trace(P, axis1=1, axis2=2) / d
    return tr

def defect_from_trace(tr, tgt):
    # ||P - c I||_{2,d}^2 = 2 - 2 Re(conj(c) tr_d P) for unitary P and |c| = 1
    return np.sqrt(np.clip(2 - 2*np.real(np.conj(tgt)*tr), 0, None))

S = load_tuple(sys.argv[2])
chk = {}
for order in ("left", "right"):
    t0 = time.time(); chk[order] = defect_from_trace(traces(S, order), sgn).max()
    print(f"convention check on {sys.argv[2]}: order {order}: max ||rho(r) - (-1)^k I||_2,d = {chk[order]:.3e} ({time.time()-t0:.0f}s)", flush=True)
order = min(chk, key=chk.get)
if chk[order] > 1e-6:
    print("NO ORDER MAKES THE SEED EXACT; aborting", flush=True); sys.exit(2)
if max(chk.values()) < 1e-6:
    print("WARNING: both orders make the seed exact; convention not discriminated", flush=True)
print("using order", order, flush=True)

for fn in sys.argv[3:]:
    t0 = time.time(); U = load_tuple(fn); d = U.shape[1]
    uni = max(np.abs(U[i].conj().T @ U[i] - np.eye(d)).max() for i in range(8))
    dfx = defect_from_trace(traces(U, order), target)
    mu, ml = dfx[~lifted].max(), dfx[lifted].max()
    q = np.quantile(dfx, [0.5, 0.99, 0.999])
    print(f"== {fn}: d={d} unitarity {uni:.1e}; ALL {N} relators: max unlifted {mu:.4f} max lifted {ml:.4f} max {max(mu, ml):.4f} "
          f"mean sq {np.mean(dfx**2):.6f} quantiles(0.5,0.99,0.999) {np.round(q, 4).tolist()} "
          f"above bar {BAR:.6f}: {int((dfx > BAR).sum())}, above 0.3: {int((dfx > 0.3).sum())} ({time.time()-t0:.0f}s)", flush=True)
    worst = np.argsort(-dfx)[:5]
    print("   worst (index, length, lift, defect):", [(int(i), int(len_of[i]), int(lifts[i]), round(float(dfx[i]), 4)) for i in worst], flush=True)
    if d % 10 == 0:
        m = d // 10; Sd = np.stack([np.kron(S[i], np.eye(m)) for i in range(8)])
        ph = np.array([np.angle(np.trace(Sd[i].conj().T @ U[i])) for i in range(8)])
        res = [np.linalg.norm(np.exp(-1j*ph[i])*U[i] - Sd[i])/np.sqrt(d) for i in range(8)]
        cob = np.abs(np.exp(1j*(E @ ph))*sgn - target).max()
        print(f"   phases vs stacked seed /2pi {np.round(ph/(2*np.pi), 5).tolist()}; residual per generator (no unitary alignment) "
              f"{np.round(res, 4).tolist()}; pure coboundary with these phases: max {cob:.4f}", flush=True)
print("DONE", flush=True)
