"""Sanity check for the Klein-four defect formulas on the universal order-pair algebra U.

Scope (read before trusting): this checks ALGEBRA ONLY.  The identities in
research/artifacts/stw01-order-pair-klein-symmetrization-2026-09-16.md, Sections 2-3,
use only three structural properties of a bounded 2-quasitrace nu on self-adjoint
elements:
    (T) nu(w + a 1) = nu(w) + a nu(1)       (a real)
    (O) nu(-w) = -nu(w)
    (H) nu(t w) = t nu(w)                   (t > 0)
The test functionals below satisfy (T), (O), (H) but are NOT quasitraces and are
deliberately nonlinear, so the defects are nonzero and the identities are tested
nontrivially.  Nothing here says anything about quasitraces themselves.

Checks:
 1. the order relations 0 <= h <= 1, 0 <= k <= h - h^2 for the rescaled pairs used;
 2. D_{nu o pi o g}(h_0, k_0) = eps * (the formula of Lemma 3.1) for g in K;
 3. the Klein sum equals eps * [E(x, y) + E(x, w_eps)];
 4. at lambda = 1/2, D_1 + D_beta = eps * E(x, y) exactly (Remark 3.2);
 5. at lambda = 1/2 the first order of D_1 + D_{beta gamma} cancels (ratio / eps^2 bounded);
 6. the eps -> 0 line identities used in Theorem 5.1 and Proposition 6.1.
"""
import numpy as np

rng = np.random.default_rng(20260916)
N = 6


def herm_contraction(n):
    a = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    h = (a + a.conj().T) / 2
    return h / np.linalg.norm(h, 2)


def nu1(w):
    ev = np.linalg.eigvalsh(w)
    return ev[-1] + ev[0] + ev.sum() / len(ev)


def nu2(w):
    ev = np.linalg.eigvalsh(w)
    return 0.7 * (ev[-2] + ev[1]) - 0.2 * (ev[-1] + ev[0]) + ev.sum()


I = np.eye(N)


def D(nu, a, b):
    return nu(a + b) - nu(a) - nu(b)


def E(nu, a, b):
    # second difference of t -> nu(b + t a) at 0, step 1
    return nu(b + a) + nu(b - a) - 2 * nu(b)


def images(h, k):
    """(pi o g)(h_0), (pi o g)(k_0) for g = 1, beta, gamma, beta gamma."""
    c = h - h @ h
    return {
        "1": (h, k),
        "beta": (I - h, k),
        "gamma": (h, c - k),
        "betagamma": (I - h, c - k),
    }


def pulled_back_defect(nu, hk):
    a, b = hk
    return nu(a + b) - nu(a) - nu(b)


maxerr = 0.0
minmargin = np.inf
lines = []
for trial in range(200):
    x = herm_contraction(N)
    y = herm_contraction(N)
    for nu in (nu1, nu2):
        # --- general lambda = 1/4, mu = 1/2, s = 3/32, eps = 1/20
        lam, s, eps = 0.25, 3.0 / 32.0, 1.0 / 20.0
        mu = 1 - 2 * lam
        h = lam * I + eps * x
        k = s * I + eps * y
        c = h - h @ h
        margins = [
            np.linalg.eigvalsh(h)[0],
            np.linalg.eigvalsh(I - h)[0],
            np.linalg.eigvalsh(k)[0],
            np.linalg.eigvalsh(c - k)[0],
        ]
        minmargin = min(minmargin, min(margins))
        w = mu * x - y - eps * x @ x
        formula = {
            "1": eps * D(nu, x, y),
            "beta": eps * D(nu, x - y, y),
            "gamma": eps * D(nu, x, w),
            "betagamma": eps * D(nu, x - w, w),
        }
        imgs = images(h, k)
        total = 0.0
        for g in imgs:
            direct = pulled_back_defect(nu, imgs[g])
            maxerr = max(maxerr, abs(direct - formula[g]))
            total += direct
        maxerr = max(maxerr, abs(total - eps * (E(nu, x, y) + E(nu, x, w))))
        # --- lambda = 1/2: exact beta formula
        lam, s, eps = 0.5, 1.0 / 8.0, 1.0 / 10.0
        h = lam * I + eps * x
        k = s * I + eps * y
        imgs = images(h, k)
        bsum = pulled_back_defect(nu, imgs["1"]) + pulled_back_defect(nu, imgs["beta"])
        maxerr = max(maxerr, abs(bsum - eps * E(nu, x, y)))

lines.append(f"trials=200 x 2 functionals, N={N}")
lines.append(f"min spectral margin of order relations (lambda=1/4, eps=1/20): {minmargin:.4e}")
lines.append(f"max |direct - formula| over all identities: {maxerr:.3e}")

# --- first-order cancellation of D_1 + D_{beta gamma} at lambda = 1/2
x = herm_contraction(N)
y = herm_contraction(N)
for eps in (1e-1, 1e-2, 1e-3):
    h = 0.5 * I + eps * x
    k = 0.125 * I + eps * y
    imgs = images(h, k)
    v = pulled_back_defect(nu1, imgs["1"]) + pulled_back_defect(nu1, imgs["betagamma"])
    base = eps * abs(D(nu1, x, y))
    lines.append(
        f"lambda=1/2 eps={eps:.0e}: |D_1+D_bg|={abs(v):.3e}  |D_1|={base:.3e}  ratio/eps^2={abs(v)/eps**2:.3f}"
    )

# --- limiting (eps -> 0) identities rewritten along the line phi(t) = nu(y + t x)
lim_err = 0.0
for trial in range(200):
    x = herm_contraction(N)
    y = herm_contraction(N)
    for nu in (nu1, nu2):
        phi = lambda t: nu(y + t * x)
        d2 = lambda t: phi(t + 1) + phi(t - 1) - 2 * phi(t)
        # Klein, lambda = 1/4: E(x,y) + E(x, x/2 - y) = d2(0) - d2(-1/2)
        lim_err = max(lim_err, abs(E(nu, x, y) + E(nu, x, x / 2 - y) - (d2(0) - d2(-0.5))))
        # gamma reversal, lambda = 1/2: D(x,y) + D(x,-y) = E(y,x)
        lim_err = max(lim_err, abs(D(nu, x, y) + D(nu, x, -y) - E(nu, y, x)))
        # beta gamma reversal, lambda = 1/4: D(x,y) + D(x - w0, w0) = phi(1)-phi(1/2)+phi(-1/2)-phi(0)
        w0 = x / 2 - y
        lim_err = max(
            lim_err,
            abs(D(nu, x, y) + D(nu, x - w0, w0) - (phi(1) - phi(0.5) + phi(-0.5) - phi(0))),
        )
        # beta gamma reversal, lambda = 1/2: D(x,y) + D(x + y, -y) = 0 identically
        lim_err = max(lim_err, abs(D(nu, x, y) + D(nu, x + y, -y)))
lines.append(f"max error in limiting line identities: {lim_err:.3e}")
maxerr = max(maxerr, lim_err)

out = "\n".join(lines)
print(out)
assert minmargin >= 0.0, "order relations violated"
assert maxerr < 1e-10, "identity mismatch"
