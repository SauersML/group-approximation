"""Exact one-qudit check of the semiclassical heuristic: K = sum_j w_j (u_j + u_j^*), u_j = e^(i pi a b/d) X^a Z^b
(the BCH-phase exponential of one quadrature) over directions (a,b) in DIRS, random weights.
c(K) = (lambda_max - s)/(W - lambda_max) with s the exact best value over all d(d+1) stabilizer states.
Prints the best c found against the triangle value, for d given on the command line."""
import numpy as np, sys
d = int(sys.argv[1]); trials = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]))
w0 = np.exp(2j*np.pi/d); X = np.roll(np.eye(d), 1, axis=0); Z = np.diag(w0**np.arange(d))
def Dm(a, b): return np.exp(1j*np.pi*a*b/d) * np.linalg.matrix_power(X, a % d) @ np.linalg.matrix_power(Z, b % d)
def D(a, b): return w0**((pow(2, -1, d)*a*b) % d) * np.linalg.matrix_power(X, a % d) @ np.linalg.matrix_power(Z, b % d)
st = [np.eye(d)[j].astype(complex) for j in range(d)]
for k in range(d):
    ev, V = np.linalg.eigh((D(1, k) + D(1, k).conj().T)/2 + 1e-3*(D(1, k) - D(1, k).conj().T)/2j)
    st += [V[:, i] for i in range(d)]
st = np.array(st)
DIRS = [(0, 1), (1, 0), (1, 1), (1, -1), (1, 2), (2, 1)]
U = [Dm(a, b) for a, b in DIRS]
def cval(w):
    K = sum(wj*(u + u.conj().T) for wj, u in zip(w, U)); W = 2*sum(w)
    lam = np.linalg.eigvalsh(K)[-1]; s = max(np.real(np.einsum('si,ij,sj->s', st.conj(), K, st)))
    return (lam - s)/(W - lam)
tri = cval([1, 1, 1, 0, 0, 0]); best = (tri, [1, 1, 1, 0, 0, 0])
for t in range(trials):
    w = rng.exponential(size=len(DIRS)) * (rng.random(len(DIRS)) < 0.7)
    if w.sum() == 0: continue
    c = cval(w)
    if c > best[0]: best = (c, list(np.round(w/w.max(), 3)))
print(f"d={d}: triangle c={tri:.4f}; best over {trials} random weightings of {DIRS}: c={best[0]:.4f} weights={best[1]}", flush=True)
