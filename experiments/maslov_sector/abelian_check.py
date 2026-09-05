"""Abelian (coboundary) relaxation of the exact metaplectic seed into the mod-3 sector, over ALL relators.
Minimizes mean_r |exp(i n(r).theta) - c_r|^2 with c_r = omega^{k_r} / (-1)^{k_r}, and separately the minimax
max_r |...|; compares with the descent minima found from the seed."""
import json, numpy as np
pres = json.load(open("pres6.json")); rels = pres["relators"]; lifts = np.array(pres["lifts"])
E = np.zeros((len(rels), 8))
for i, r in enumerate(rels):
    for x in r: E[i, x % 8] += 1 if x < 8 else -1
c = np.exp(2j*np.pi*(lifts % 3)/3) / ((-1.0)**lifts)
rng = np.random.default_rng(0)
def energy(th): 
    ph = np.exp(1j*(E @ th)); D = ph - c; return np.mean(np.abs(D)**2), np.abs(D).max(), D, ph
best = None
for rep in range(30):
    th = rng.uniform(0, 2*np.pi, 8); eta = 0.05
    e, mx, D, ph = energy(th)
    for it in range(3000):
        g = np.mean(2*np.real(np.conj(D) * 1j*ph)[:, None] * E, axis=0)
        th2 = th - eta*g; e2, mx2, D2, ph2 = energy(th2)
        if e2 < e: th, e, mx, D, ph = th2, e2, mx2, D2, ph2; eta *= 1.1
        else: eta *= 0.5
        if eta < 1e-13: break
    if best is None or e < best[0]: best = (e, mx, th.copy())
print(f"mean-square abelian relaxation over all {len(rels)} relators: mean sq defect {best[0]:.6f}, max defect {best[1]:.4f}, theta/2pi = {np.round(best[2]/(2*np.pi) % 1, 4).tolist()}", flush=True)
# unique exponent-sum vectors: the abelian problem lives on them
keys = {}
for i in range(len(rels)): keys.setdefault((tuple(E[i].astype(int)), int(lifts[i] % 3)), 0); keys[(tuple(E[i].astype(int)), int(lifts[i] % 3))] += 1
print("distinct (exponent vector, lift mod 3) pairs:", len(keys), flush=True)
# minimax via subgradient / smoothed max (log-sum-exp) from the mean-square optimum and random starts
def smooth(th, beta):
    ph = np.exp(1j*(E @ th)); sq = np.abs(ph - c)**2
    m = sq.max(); w = np.exp(beta*(sq - m)); 
    val = m + np.log(w.mean())/beta
    D = ph - c; g = ((w/w.sum())[:, None] * (2*np.real(np.conj(D) * 1j*ph))[:, None] * E).sum(axis=0)
    return val, g, np.sqrt(m)
bestm = None
starts = [best[2]] + [rng.uniform(0, 2*np.pi, 8) for _ in range(20)]
for th in starts:
    th = th.copy()
    for beta in (20, 50, 100, 200, 400):
        eta = 0.02
        val, g, mx = smooth(th, beta)
        for it in range(1500):
            th2 = th - eta*g; val2, g2, mx2 = smooth(th2, beta)
            if val2 < val: th, val, g, mx = th2, val2, g2, mx2; eta *= 1.1
            else: eta *= 0.5
            if eta < 1e-12: break
    e_, mx_, _, _ = energy(th)
    if bestm is None or mx_ < bestm[1]: bestm = (e_, mx_, th.copy())
print(f"minimax abelian relaxation over all relators: max defect {bestm[1]:.4f} (mean sq {bestm[0]:.6f}), theta/2pi = {np.round(bestm[2]/(2*np.pi) % 1, 4).tolist()}", flush=True)
# compare with the descent minimum: energy of the theta seed rescaled by the descent's phases
U = np.load("best_m3_seed_seed_theta_d10.json_d10_eps0.2_seed7.npy")
J = json.load(open("seed_theta_d10.json")); a = np.array(J["seed"]); S = (a[:,:,0]+1j*a[:,:,1]).reshape(8, 10, 10)
A = sum(S[i] @ U[i].conj().T for i in range(8)); W, _, Vh = np.linalg.svd(A); Q = W @ Vh
V = np.stack([Q @ U[i] @ Q.conj().T for i in range(8)])
ph = np.array([np.angle(np.trace(S[i].conj().T @ V[i])) for i in range(8)])
print("descent minimizer: generator phases relative to the seed, /2pi:", np.round(ph/(2*np.pi) % 1, 4).tolist(), flush=True)
print("residual after removing the phases, per generator normalized-HS:", np.round([np.linalg.norm(np.exp(-1j*ph[i])*V[i] - S[i])/np.sqrt(10) for i in range(8)], 4).tolist(), flush=True)
e_desc = energy(ph)
print(f"pure coboundary with the descent's phases: mean sq defect {e_desc[0]:.6f}, max {e_desc[1]:.4f} (descent minimizer itself: 0.012462, 0.4384)", flush=True)
