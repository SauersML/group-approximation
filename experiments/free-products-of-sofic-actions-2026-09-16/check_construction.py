"""Finite sanity check of the construction in
research/free-products-of-sofic-actions-are-sofic-proof.md (Steps 2-7).

G = C2 * C3 = <a> * <b> acting on X = {0,1,2} by a=(0 1), b=(0 1 2).
Factor models: A_j = G_j x [K], phi_j(h)(p,k) = (h p, k), labels
Lambda_(p,k)(y) = alpha(p^-1) y, good sets S_j = A_j minus random points.
We build the randomized models, the label matching, phi on reduced words,
S and S°, and verify the orbit identity exactly on S° and multiplicativity.
Single-threaded, a few seconds.
"""
import itertools, random
import numpy as np

random.seed(1); np.random.seed(1)
X = [0, 1, 2]; nX = 3
sig = {1: [1, 0, 2], 2: [1, 2, 0]}          # generator permutations a, b
order = {1: 2, 2: 3}
def act(j, e, y):                            # alpha(gen_j^e) y
    for _ in range(e % order[j]): y = sig[j][y]
    return y
K = 10
Bp = 3                                       # |B'|
L = Bp ** nX
T = Bp ** nX                                 # tau: X -> B' encoded base Bp (B_j = X)
def tau_val(tau, y): return (tau // Bp ** y) % Bp
def enc(f): return sum(f[y] * Bp ** y for y in range(nX))
models = {}
for j in (1, 2):
    Aj = [(p, k) for p in range(order[j]) for k in range(K)]
    Sj = set(random.sample(Aj, int(0.9 * len(Aj))))
    models[j] = (Aj, Sj)
N = (2 * K * T) * (3 * K * T)
M = {1: N // (2 * K * T), 2: N // (3 * K * T)}
def idx(j, p, k, tau, r): return (((p * K + k) * T + tau) * M[j] + r)
def unidx(j, i):
    i, r = divmod(i, M[j]); i, tau = divmod(i, T); p, k = divmod(i, K); return p, k, tau, r
# phi'_j(gen^e), S'_j, lambda^j as arrays over A'_j
phi_p, good, lab = {}, {}, {}
for j in (1, 2):
    ar = np.arange(N)
    r = ar % M[j]; q = ar // M[j]; tau = q % T; q //= T; k = q % K; p = q // K
    phi_p[j] = {e: ((((p + e) % order[j]) * K + k) * T + tau) * M[j] + r for e in range(order[j])}
    S_set = models[j][1]
    good[j] = np.array([(int(pp), int(kk)) in S_set for pp, kk in zip(p[: 2 * K * T * 0 + order[j] * K * T * M[j]:1][:0], [])], dtype=bool) if False else None
    gmask = np.zeros(order[j] * K, dtype=bool)
    for (pp, kk) in S_set: gmask[pp * K + kk] = True
    good[j] = gmask[p * K + k]
    # label: y -> tau(Lambda_p(y)) = tau(alpha(p^-1) y)
    labv = np.zeros(N, dtype=np.int64)
    for y in range(nX):
        lam = np.array([act(j, -pp, y) for pp in range(order[j])])[p]
        labv += ((tau // (Bp ** lam)) % Bp) * Bp ** y
    lab[j] = labv
# (R3) uniformity check
for j in (1, 2):
    cnt = np.bincount(lab[j][good[j]], minlength=L)
    assert cnt.min() == cnt.max() == good[j].sum() // L, "R3 fails"
# matching beta_2 : A = A'_1 -> A'_2
beta = np.full(N, -1, dtype=np.int64)
D2 = np.zeros(N, dtype=bool)
for c in range(L):
    src = np.nonzero(good[1] & (lab[1] == c))[0]; dst = np.nonzero(good[2] & (lab[2] == c))[0]
    n = min(len(src), len(dst)); beta[src[:n]] = dst[:n]; D2[src[:n]] = True
unused = np.setdiff1d(np.arange(N), beta[beta >= 0]); rest = np.nonzero(beta < 0)[0]
beta[rest] = unused
binv = np.empty(N, dtype=np.int64); binv[beta] = np.arange(N)
psi = {(1, e): phi_p[1][e] for e in range(2)}
psi.update({(2, e): binv[phi_p[2][e][beta]] for e in range(3)})
def perm_of_word(w):                         # w = list of (j,e); product psi(w1)...psi(wk)
    P = np.arange(N)
    for (j, e) in reversed(w): P = psi[(j, e)][P]
    return P
words = [[]]
for ln in range(1, 4):
    for js in itertools.product((1, 2), repeat=ln):
        if any(js[t] == js[t + 1] for t in range(ln - 1)): continue
        for es in itertools.product(*[range(1, order[j]) for j in js]):
            words.append(list(zip(js, es)))
def word_act_inv(w, x):                      # g^-1 x for g = w1...wk
    for (j, e) in w: x = act(j, -e, x)
    return x
inj = np.array([len({(c // Bp ** y) % Bp for y in range(nX)}) == nX for c in range(L)])
S = D2 & good[1] & inj[lab[1]]
So = S.copy()
for w in words:
    for t in range(len(w)): So &= S[perm_of_word(w[t:])]
print("N", N, "|S|/N", S.mean(), "|S°|/N", So.mean(), "#words", len(words))
bad = 0
for w in words:
    P = perm_of_word(w)
    for x in X:
        gx = word_act_inv(w, x)
        lhs = (lab[1][P[So]] // Bp ** x) % Bp; rhs = (lab[1][So] // Bp ** gx) % Bp
        bad += int((lhs != rhs).sum())
print("orbit identity violations on S°:", bad)
def reduce(w):
    out = []
    for (j, e) in w:
        if out and out[-1][0] == j:
            e2 = (out[-1][1] + e) % order[j]; out.pop()
            if e2: out.append((j, e2))
        else: out.append((j, e))
    return out
maxd = 0.0
for g in words:
    for h in words:
        d = (perm_of_word(reduce(g + h)) != perm_of_word(g)[perm_of_word(h)]).mean(); maxd = max(maxd, d)
print("max multiplicativity defect (exact factor models):", maxd)

# Ablation: replace the label matching by an arbitrary bijection. The chained
# identity should then fail on most points, which shows the check has power.
rng = np.random.default_rng(2)
beta_r = rng.permutation(N); binv_r = np.empty(N, dtype=np.int64); binv_r[beta_r] = np.arange(N)
for e in range(3): psi[(2, e)] = binv_r[phi_p[2][e][beta_r]]
S_r = good[1] & good[2][beta_r] & inj[lab[1]]
bad_r = 0; tot = 0
for w in words:
    m = S_r.copy()
    for t in range(len(w)): m &= S_r[perm_of_word(w[t:])]
    P = perm_of_word(w)
    for x in X:
        gx = word_act_inv(w, x)
        bad_r += int(((lab[1][P[m]] // Bp ** x) % Bp != (lab[1][m] // Bp ** gx) % Bp).sum()); tot += int(m.sum())
print("ablation (unmatched bijection, per-word suffix-good points): violations", bad_r, "of", tot, "checks")
