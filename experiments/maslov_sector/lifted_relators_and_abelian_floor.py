import json, numpy as np
pres = json.load(open("pres6.json"))
names = pres["root_names"]
def letter(a): return names[a] if a < 8 else "(" + names[a-8] + ")^-1"
lifted = [(r, k) for r, k in zip(pres["relators"], pres["lifts"]) if k != 0]
print(len(lifted), "lifted relators", flush=True)
for r, k in lifted:
    print(k, " ".join(letter(a) for a in r), flush=True)
from collections import Counter
print("relator length histogram:", sorted(Counter(len(r) for r in pres["relators"]).items()), flush=True)
# abelian floor: minimize mean over relators of |exp(i<n,theta>) - c|^2 by random-restart gradient descent on theta in R^8
idx_l = [i for i,k in enumerate(pres["lifts"]) if k != 0]
idx_u = [i for i,k in enumerate(pres["lifts"]) if k == 0]
rng0 = np.random.default_rng(1); idx = idx_l + list(rng0.choice(idx_u, size=3000, replace=False))
rels = [pres["relators"][i] for i in idx]; lifts = np.array([pres["lifts"][i] for i in idx])
N = np.zeros((len(rels), 8))
for i, r in enumerate(rels):
    for a in r: N[i, a % 8] += 1 if a < 8 else -1
rng = np.random.default_rng(0)
for m in (2, 3):
    c = np.exp(2j*np.pi*(lifts % m)/m)
    best = None
    for rep in range(40):
        th = rng.uniform(0, 2*np.pi, 8); eta = 0.05
        for it in range(800):
            ph = np.exp(1j*(N @ th)); D = ph - c
            e = np.mean(np.abs(D)**2)
            g = np.mean(2*np.real(np.conj(D) * 1j*ph)[:, None] * N, axis=0)
            th2 = th - eta*g
            ph2 = np.exp(1j*(N @ th2)); e2 = np.mean(np.abs(ph2 - c)**2)
            if e2 < e: th = th2; eta *= 1.1
            else: eta *= 0.5
            if eta < 1e-12: break
        ph = np.exp(1j*(N @ th)); D = np.abs(ph - c)
        cand = (np.mean(D**2), D.max(), th)
        if best is None or cand[0] < best[0]: best = cand
    print(f"abelian relaxation mod {m} (all lifted + 3000 sampled unlifted relators): best mean sq defect = {best[0]:.6f}, max defect = {best[1]:.4f}, theta/pi = {np.round(best[2]/np.pi % 2, 4).tolist()}", flush=True)
