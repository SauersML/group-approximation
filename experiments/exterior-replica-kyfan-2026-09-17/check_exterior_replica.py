"""Numerical sanity checks for exterior-replica-converts-kyfan-witnesses-to-opnorm.

Checks, on random and adversarial unitaries:
  (1) the compound matrix C_j(g) (all j x j minors) is unitary and multiplicative;
  (2) l_op(Phi_k g) <= KF_k(g) always, and l_op(Phi_k g) >= KF_k(g)/pi when KF_k(g) <= 2;
  (3) the reduction lemma: some j <= k gives op ratio <= pi * rho / min(A, 1);
  (4) the gauge reduction: a ratio in a unitarily invariant norm gives a Ky Fan index
      with ratio <= |R0| * (that ratio).
KF_k(g) is the Ky Fan k-norm of g - I (sum of the k largest |lambda_i - 1|).
"""
import itertools
import numpy as np

rng = np.random.default_rng(20260919)


def haar(d):
    z = (rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def near_id(d, scale):
    h = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    h = (h + h.conj().T) / 2
    w, v = np.linalg.eigh(h)
    return v @ np.diag(np.exp(1j * scale * w)) @ v.conj().T


def compound(g, j):
    d = g.shape[0]
    subs = list(itertools.combinations(range(d), j))
    c = np.empty((len(subs), len(subs)), dtype=complex)
    for a, s in enumerate(subs):
        for b, t in enumerate(subs):
            c[a, b] = np.linalg.det(g[np.ix_(s, t)])
    return c


def phi(g, k):
    blocks = [compound(g, j) for j in range(1, k + 1)]
    n = sum(b.shape[0] for b in blocks)
    out = np.zeros((n, n), dtype=complex)
    i = 0
    for b in blocks:
        m = b.shape[0]
        out[i:i + m, i:i + m] = b
        i += m
    return out


def lop(g):
    return np.linalg.norm(g - np.eye(g.shape[0]), 2)


def svals(g):
    return np.sort(np.abs(np.linalg.eigvals(g) - 1))[::-1]


def kf(g, k):
    return float(np.sum(svals(g)[:k]))


worst = {"hom": 0.0, "unit": 0.0, "upper": -1e9, "lower": 1e9, "reduction": 0.0, "gauge": 0.0}
d = 5
for trial in range(300):
    scale = [0.02, 0.1, 0.4, 1.5, 4.0][trial % 5]
    g, h = near_id(d, scale), (haar(d) if trial % 2 else near_id(d, scale))
    k = 1 + trial % d
    # (1) homomorphism and unitarity
    for j in range(1, d + 1):
        cg, ch, cgh = compound(g, j), compound(h, j), compound(g @ h, j)
        worst["hom"] = max(worst["hom"], np.abs(cg @ ch - cgh).max())
        worst["unit"] = max(worst["unit"], np.abs(cg @ cg.conj().T - np.eye(cg.shape[0])).max())
    # (2) two-sided comparison
    pg = phi(g, k)
    worst["upper"] = max(worst["upper"], lop(pg) - kf(g, k))
    if kf(g, k) <= 2:
        worst["lower"] = min(worst["lower"], lop(pg) - kf(g, k) / np.pi)
    # (3) reduction lemma with a = g, relators = {h, g h g^-1 h}
    rels = [h, g @ h @ g.conj().T @ h]
    A = kf(g, k)
    rho = max(kf(r, k) for r in rels)
    if A > 1e-9:
        js = [j for j in range(1, k + 1) if kf(g, j) <= 2]
        j = k if A <= 2 else max(js)
        pa = lop(phi(g, j))
        ratio = max(lop(phi(r, j)) for r in rels) / pa
        bound = np.pi * rho / min(A, 1.0)
        worst["reduction"] = max(worst["reduction"], ratio / bound)
    # (4) gauge reduction for Schatten p and a random symmetric gauge (max of weighted Ky Fan sums)
    wts = [np.sort(rng.random(d))[::-1] for _ in range(3)]
    gauges = [lambda x, p=p: float(np.sum(x ** p) ** (1 / p)) for p in (1.0, 1.5, 3.0)]
    gauges.append(lambda x: float(max(np.dot(w, np.sort(x)[::-1]) for w in wts)))
    for N in gauges:
        eps = max(N(svals(r)) for r in rels) / N(svals(g))
        best = min(max(kf(r, kk) for r in rels) / kf(g, kk) for kk in range(1, d + 1))
        worst["gauge"] = max(worst["gauge"], best / (len(rels) * eps))

print("max |C(g)C(h) - C(gh)|              :", f"{worst['hom']:.2e}")
print("max |C(g)C(g)^* - I|                 :", f"{worst['unit']:.2e}")
print("max l_op(Phi_k g) - KF_k(g)  (<= 0)  :", f"{worst['upper']:.3e}")
print("min l_op(Phi_k g) - KF_k/pi  (>= 0)  :", f"{worst['lower']:.3e}")
print("max op-ratio / (pi rho/min(A,1)) (<=1):", f"{worst['reduction']:.4f}")
print("max best-KF-ratio / (|R0| eps)  (<=1):", f"{worst['gauge']:.4f}")

# (5) eigenvalue-level example: a has k angles 1/k; r has one angle k^-1/2 and k^3 angles k^-2.
# At the identity replica the op, HS and rank ratios r/a all fail (>= 1); Phi_k gives op ratio ~ pi k^-1/2.
def s_of(angles):
    return 2 * np.abs(np.sin(np.asarray(angles) / 2))


def lop_phi_from_angles(angles, k):
    th = np.sort(np.asarray(angles))
    pos = np.sort(th[th > 0])[::-1][:k]
    neg = np.sort(-th[th < 0])[::-1][:k]
    best = 0.0
    for part in (pos, neg):
        cs = np.cumsum(part) if part.size else np.array([0.0])
        best = max(best, float(np.max(2 * np.abs(np.sin(cs / 2)))))
    return best


print("example (5): k, op-ratio, HS-ratio, rank-ratio at identity; KF_k ratio; op-ratio after Phi_k; bound")
ex_ok = True
for k in (10, 20, 40):
    a_ang = np.full(k, 1.0 / k)
    r_ang = np.concatenate([[k ** -0.5], np.full(k ** 3, float(k) ** -2)])
    sa, sr = s_of(a_ang), s_of(r_ang)
    op_r = sr.max() / sa.max()
    hs_r = np.sqrt(np.sum(sr ** 2) / np.sum(sa ** 2))
    rk_r = r_ang.size / a_ang.size
    kfa, kfr = np.sort(sa)[::-1][:k].sum(), np.sort(sr)[::-1][:k].sum()
    phi_r = lop_phi_from_angles(r_ang, k) / lop_phi_from_angles(a_ang, k)
    bound = np.pi * kfr / min(kfa, 1.0)
    print(f"  k={k:3d}  op={op_r:.3f} HS={hs_r:.3f} rank={rk_r:.0f}  KF={kfr/kfa:.4f}  Phi_k op={phi_r:.4f}  bound={bound:.4f}")
    ex_ok = ex_ok and op_r >= 1 and hs_r >= 1 and rk_r >= 1 and phi_r <= bound + 1e-12
print("example (5) consistent" if ex_ok else "example (5) FAILED")

ok = ex_ok and (worst["hom"] < 1e-9 and worst["unit"] < 1e-9 and worst["upper"] < 1e-9
      and worst["lower"] > -1e-9 and worst["reduction"] <= 1 + 1e-9 and worst["gauge"] <= 1 + 1e-9)
print("ALL CHECKS PASS" if ok else "CHECK FAILED")
