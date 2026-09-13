"""Abelian (coboundary) bar as a function of the twist theta, for Sp4(Z) root presentation (pres6.json).

For an exact seed rho with rho(r) = s_r I on every relator (s_r = (-1)^{k_r} for the metaplectic theta models,
s_r = 1 for a genuine representation), rescale generators by phases e^{i phi_s}.  Then rho'(r) = e^{i <e_r, phi>} s_r I,
and the theta-sector target is e^{2 pi i theta k_r} I.  The normalized-HS defect of relator r is
|e^{i <e_r, phi>} s_r - e^{2 pi i theta k_r}|, independent of the dimension of the seed.  The minimax over phi is an
explicit upper bound on the least maximal relator defect in the theta sector, in every dimension carrying the seed
(4a + 10b for the metaplectic class, every d for the trivial one).  NUMERICS: this is an upper bound only; it can never
certify a lower bound or non-hyperlinearity.
Usage: python3 theta_bar_profile.py pres6.json out.tsv"""
import json, sys, numpy as np

pres = json.load(open(sys.argv[1]))
rels, lifts = pres["relators"], np.array(pres["lifts"], dtype=np.int64)
E = np.zeros((len(rels), 8))
for i, r in enumerate(rels):
    for x in r:
        E[i, x % 8] += 1 if x < 8 else -1
# collapse identical (exponent vector, lift) rows: the abelian problem only sees these
key = np.concatenate([E, lifts[:, None]], axis=1)
uniq, counts = np.unique(key, axis=0, return_counts=True)
Eu, ku = uniq[:, :8], uniq[:, 8]
print(f"relators {len(rels)}, distinct (exponent vector, lift) rows {len(uniq)}, lift values {sorted(set(ku.astype(int).tolist()))}", flush=True)

def smooth(phi, c, beta):
    ph = np.exp(1j * (Eu @ phi)); D = ph - c; sq = np.abs(D) ** 2
    m = sq.max(); w = np.exp(beta * (sq - m)); w = w / w.sum()
    val = m + np.log(np.mean(np.exp(beta * (sq - m)))) / beta
    g = (w[:, None] * (2 * np.real(np.conj(D) * 1j * ph))[:, None] * Eu).sum(axis=0)
    return val, g, np.sqrt(m)

def minimax(c, rng, nstart=24):
    best = None
    starts = [np.zeros(8)] + [rng.uniform(-np.pi, np.pi, 8) for _ in range(nstart - 1)]
    for phi in starts:
        phi = phi.copy()
        for beta in (20, 50, 100, 200, 400, 800):
            eta = 0.02; val, g, mx = smooth(phi, c, beta)
            for _ in range(2000):
                p2 = phi - eta * g; v2, g2, m2 = smooth(p2, c, beta)
                if v2 < val: phi, val, g, mx = p2, v2, g2, m2; eta *= 1.1
                else: eta *= 0.5
                if eta < 1e-13: break
        mx = np.abs(np.exp(1j * (Eu @ phi)) - c).max()
        if best is None or mx < best[0]: best = (mx, phi.copy())
    return best

rng = np.random.default_rng(20260913)
thetas = [0.5, 0.49, 0.45, 0.4, 1/3, 0.3, 0.25, 0.2, 1/6, 0.1, 0.05, 0.0, (np.sqrt(5) - 1) / 2 % 1, np.sqrt(2) % 1]
out = open(sys.argv[2], "w")
out.write("seed\ttheta\tbar_max_defect\tphi_over_2pi\n")
for seed_name, s in (("metaplectic", (-1.0) ** ku), ("trivial", np.ones_like(ku))):
    for th in thetas:
        c = np.exp(2j * np.pi * th * ku) / s
        mx, phi = minimax(c, rng)
        line = f"{seed_name}\t{th:.6f}\t{mx:.6f}\t{np.round((phi / (2*np.pi) + 0.5) % 1 - 0.5, 5).tolist()}"
        print(line, flush=True); out.write(line + "\n"); out.flush()
out.close()
print("DONE", flush=True)
