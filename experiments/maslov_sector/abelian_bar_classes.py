"""Minimax coboundary bar for the mod-3 sector from each finite-dimensionally realized class:
trivial, metaplectic (-1)^k, spin (-1)^s, and spin x metaplectic (-1)^{s+k}; over ALL relators."""
import json, numpy as np
pres = json.load(open("pres6.json")); rels = pres["relators"]; lifts = np.array(pres["lifts"])
sp = json.load(open("spin_phases.json"))["phases"]; s_ = np.array([0 if p is None else p for p in sp])
assert all(p is not None for p in sp)
E = np.zeros((len(rels), 8))
for i, r in enumerate(rels):
    for x in r: E[i, x % 8] += 1 if x < 8 else -1
rng = np.random.default_rng(0)
def run(c, label):
    def energy(th):
        ph = np.exp(1j*(E @ th)); D = np.abs(ph - c); return np.mean(D**2), D.max()
    def smooth(th, beta):
        ph = np.exp(1j*(E @ th)); sq = np.abs(ph - c)**2
        m = sq.max(); w = np.exp(beta*(sq - m)); val = m + np.log(w.mean())/beta
        D = ph - c; g = ((w/w.sum())[:, None] * (2*np.real(np.conj(D) * 1j*ph))[:, None] * E).sum(axis=0)
        return val, g
    best = None
    for st in range(16):
        th = np.zeros(8) if st == 0 else rng.uniform(0, 2*np.pi, 8)
        for beta in (20, 50, 100, 200, 400):
            eta = 0.02; val, g = smooth(th, beta)
            for it in range(1200):
                th2 = th - eta*g; val2, g2 = smooth(th2, beta)
                if val2 < val: th, val, g = th2, val2, g2; eta *= 1.1
                else: eta *= 0.5
                if eta < 1e-12: break
        e, mx = energy(th)
        if best is None or mx < best[1]: best = (e, mx, th.copy())
    print(f"{label}: minimax coboundary bar over all relators: max defect {best[1]:.4f} (mean sq {best[0]:.6f}), theta/2pi = {np.round(best[2]/(2*np.pi) % 1, 4).tolist()}", flush=True)
omega = np.exp(2j*np.pi*(lifts % 3)/3)
run(omega, "trivial class")
run(omega / ((-1.0)**lifts), "metaplectic class")
run(omega / ((-1.0)**s_), "spin class")
run(omega / ((-1.0)**(s_ + lifts)), "spin x metaplectic class")
