# One-qudit measurement rounding: for a pure state psi on C^d let mu_l = max_{v in l, v != 0} |<psi|D(v)|psi>|
# over the d+1 lines l of F_d^2, eps_l = 1 - mu_l, and c_meas(psi) = least c with
#     sum_l (1 - c eps_l/(1 - eps_l))_+ <= 1.
# Measuring psi in the eigenbasis of a random line (line l with probability lambda_l) shows
# c^(1)_d <= sup_psi c_meas(psi).  Here: local search for sup_psi c_meas(psi).
import numpy as np, sys
from scipy.optimize import minimize
d = int(sys.argv[1]); restarts = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
rng = np.random.default_rng(seed)
x = np.arange(d)
lines = [[(0, b) for b in range(1, d)]] + [[(m, (m*s) % d) for m in range(1, d)] for s in range(d)]
LA = [np.array([p[0] for p in l]) for l in lines]; LB = [np.array([p[1] for p in l]) for l in lines]

def chi_abs(psi):
    psi = psi/np.linalg.norm(psi)
    M = np.array([np.conj(np.roll(psi, -a))*psi for a in range(d)])   # row a: conj psi(x+a) psi(x)
    return np.abs(np.fft.ifft(M, axis=1)*d)                           # [a,b] = |sum_x e^{2pi i bx/d} ...|

def mus(psi):
    C = chi_abs(psi); return np.array([C[LA[i], LB[i]].max() for i in range(d+1)])

def cmeas_from_mu(mu):
    mu = np.minimum(mu, 1-1e-15)
    r = mu/(1-mu)                      # 1 - c eps/(1-eps) = 1 - c/r ;  need sum (1 - c/r)_+ <= 1
    lo, hi = 0.0, 1e6
    for _ in range(200):
        c = (lo+hi)/2
        if np.maximum(0, 1 - c/r).sum() > 1: lo = c
        else: hi = c
    return hi

def f(p):
    psi = p[:d] + 1j*p[d:]
    return -cmeas_from_mu(mus(psi))

def gauss(a, b, x0=0.0):
    xs = ((x + d//2) % d) - d//2
    g = np.exp(-np.pi*(a - 1j*b)*(xs - x0)**2/d); return np.concatenate([g.real, g.imag])

best = (0, None)
seeds = [gauss(np.sqrt(3)/2, 0.5), gauss(1.0, 0.0), gauss(np.sqrt(3)/2, -0.5)]
for t in range(restarts):
    p0 = seeds[t] if t < len(seeds) else (seeds[t % 3] + rng.normal(size=2*d)*0.3*rng.random() if t % 2 else rng.normal(size=2*d))
    r = minimize(f, p0, method='Nelder-Mead', options={'maxiter': 20000*d, 'maxfev': 20000*d, 'xatol': 1e-10, 'fatol': 1e-12, 'adaptive': True})
    r = minimize(f, r.x, method='Powell', options={'maxiter': 20000, 'xtol': 1e-10, 'ftol': 1e-13})
    if t < len(seeds): print('seed %d: start %.6f -> %.6f' % (t, -f(p0), -r.fun), flush=True)
    if -r.fun > best[0]: best = (-r.fun, r.x)
print('d=%d  sup c_meas >= %.6f   triangle 2d/(sqrt3 pi) = %.6f   d/pi = %.6f' % (d, best[0], 2*d/(np.sqrt(3)*np.pi), d/np.pi))
mu = mus(best[1][:d]+1j*best[1][d:]); print('mu sorted', np.round(np.sort(mu)[::-1][:6], 6))
