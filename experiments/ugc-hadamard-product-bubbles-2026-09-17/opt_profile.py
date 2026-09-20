"""Minimax over profiles g of the limit price of the product adversary P_g.

Configurations are compiled into padded arrays so that the price of every
(config, edge type) is evaluated in one vectorized pass.  g is piecewise
linear on knots W (g(0) = 0, g(1) = 1 fixed); slopes at a knot use the larger
one-sided slope (conservative).  Prints the best max price found and the
worst configurations.
"""
import sys
import itertools
import numpy as np
from scipy.optimize import minimize
from limit_product import chi_table

PAD = 64


def compile_config(f, C, tag):
    V = len(f)
    fh = C @ f / V
    keep = np.abs(fh) > 1e-12
    Ck, fk = C[keep], fh[keep]
    bw, bp = [], []
    for v in range(V):
        for s in (1, -1):
            p = (1 + s * f[v]) / 2 / V
            if p > 1e-15:
                bw.append(s * Ck[:, v] * fk); bp.append(p)
    ew = []
    for u in range(V):
        for sg in (1, -1):
            if (1 + sg * f[u]) / 2 > 1e-15:
                ew.append(sg * Ck[:, u] * fk)
    return tag, bw, bp, ew


class Bank:
    def __init__(self, configs):
        self.tags = []
        bW, bP, bC, eW, eC = [], [], [], [], []
        for ci, (tag, bw, bp, ew) in enumerate(configs):
            self.tags.append(tag)
            for w, p in zip(bw, bp):
                row = np.full(PAD, -1.0); row[:len(w)] = w
                bW.append(row); bP.append(p); bC.append(ci)
            for w in ew:
                row = np.full(PAD, -1.0); row[:len(w)] = w
                eW.append(row); eC.append(ci)
        self.bW, self.bP, self.bC = np.array(bW), np.array(bP), np.array(bC)
        self.eW, self.eC = np.array(eW), np.array(eC)
        self.n = len(configs)

    def prices(self, W, G):
        sl = np.diff(G) / np.diff(W)

        def val(w):
            return np.where(w <= 0, 0.0, np.interp(np.clip(w, 0, 1), W, G))

        def slope(w):
            wc = np.clip(w, 0, 1)
            r = np.clip(np.searchsorted(W, wc, side="right") - 1, 0, len(sl) - 1)
            l = np.clip(np.searchsorted(W, wc, side="left") - 1, 0, len(sl) - 1)
            return np.where(w < 0, 0.0, np.maximum(np.abs(sl[r]), np.abs(sl[l])))

        g = val(self.bW); d = slope(self.bW)
        Bt = self.bP * np.prod(1 - g / 2, axis=1) * np.sum(2 * d / (2 - g), axis=1)
        B = np.bincount(self.bC, weights=Bt, minlength=self.n)
        Px = np.prod(1 - val(self.eW) / 2, axis=1)
        Py = np.prod(1 - val(-self.eW) / 2, axis=1)
        A = 1 - Px - Py + 2 * Px * Py
        return A + B[self.eC], self.eC


def default_configs(lams, m_bool=(3, 4)):
    cfgs = []
    C1 = chi_table(1)
    for c in lams:
        cfgs.append(compile_config(np.array([c, -c]), C1, ("pin", c)))
    C2 = chi_table(2)
    for lam in lams:
        cfgs.append(compile_config(lam * np.array([1., 1, 1, -1]), C2, ("bent2", lam)))
    C4 = chi_table(4)
    b4 = np.array([(-1.0) ** (((v & 1) * ((v >> 1) & 1) + ((v >> 2) & 1) * ((v >> 3) & 1)) % 2) for v in range(16)])
    for lam in lams:
        cfgs.append(compile_config(lam * b4, C4, ("bent4", lam)))
    for m in m_bool:
        Cm = chi_table(m)
        for line in open(f"reps_k{m}.txt"):
            h = int(line.split()[0], 16)
            base = np.array([-1.0 if (h >> z) & 1 else 1.0 for z in range(1 << m)])
            for lam in lams:
                cfgs.append(compile_config(lam * base, Cm, (f"rep{m}:{h:x}", lam)))
    for vals in itertools.product((1, 0.5, 0, -0.5, -1), repeat=4):
        f = np.array(vals, float)
        if np.allclose(C2 @ f, 0):
            continue
        cfgs.append(compile_config(f, C2, ("frac2", vals)))
    return cfgs


def run(nk=48, seed=0, iters=6):
    lams = np.linspace(0.05, 1.0, 20)
    bank = Bank(default_configs(lams))
    W = np.linspace(0, 1, nk + 1) + 0.0
    W[1:-1] += 0.37 / nk  # keep dyadic levels off the knots
    rng = np.random.default_rng(seed)
    G0 = np.clip((W - 0.25) / 0.75, 0, 1) ** 2

    def mx(Gin):
        G = np.concatenate([[0.0], Gin, [1.0]])
        p, _ = bank.prices(W, G)
        return p

    def soft(Gin, beta):
        p = mx(np.clip(Gin, 0, 1))
        m = p.max()
        return m + np.log(np.exp(beta * (p - m)).sum()) / beta

    x = G0[1:-1]
    for beta in (20, 60, 200, 600):
        res = minimize(soft, x, args=(beta,), method="L-BFGS-B", bounds=[(0, 1)] * len(x),
                       options={"maxiter": 400})
        x = res.x
        print(f"beta={beta}: max price {mx(x).max():.4f}", flush=True)
    G = np.concatenate([[0.0], x, [1.0]])
    p, ec = bank.prices(W, G)
    order = np.argsort(-p)
    seen = set()
    print("worst configurations:")
    for o in order:
        t = bank.tags[ec[o]]
        if t in seen:
            continue
        seen.add(t)
        print(f"  {p[o]:.4f} {t}")
        if len(seen) >= 12:
            break
    print("profile:", " ".join(f"{w:.3f}:{g:.3f}" for w, g in zip(W, G)))
    return p.max()


if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 48)
