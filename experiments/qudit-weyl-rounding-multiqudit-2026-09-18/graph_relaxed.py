# Relaxed semiclassical test on arbitrary noncommutation graphs.
# For graph G, sign pattern S on edges, and weights w >= 0, let
#   F(w) = min sum_j w_j Q_jj  over real Q, Omega with Q + i Omega PSD,
#          S_jk Omega_jk >= 1 on edges, Omega_jk = 0 on non-edges        ( = min ||D Omega D||_1 )
# and test F(w) >= sqrt3 (W - alpha_w(G)).  Alternate SDP in (Q,Omega) and LP in w.
import numpy as np, cvxpy as cp, sys
from scipy.optimize import linprog
rng = np.random.default_rng(int(sys.argv[1]))
N = int(sys.argv[2]); trials = int(sys.argv[3]); pedge = float(sys.argv[4]) if len(sys.argv)>4 else 0.6
r3 = np.sqrt(3)

def max_indep(A):
    N = len(A); res = []
    for mask in range(1, 1<<N):
        idx = [i for i in range(N) if mask>>i & 1]
        if all(A[i,j]==0 for i in idx for j in idx if i<j): res.append(mask)
    mx = [s for s in res if not any((s|t)==t and s!=t for t in res)]
    return np.array([[(s>>i)&1 for i in range(N)] for s in mx], float)

def sdp(w, A, S):
    N = len(A); Q = cp.Variable((N,N), symmetric=True); O = cp.Variable((N,N))
    M = cp.bmat([[Q, -O],[O, Q]])
    cons = [M >> 0, O == -O.T]
    for j in range(N):
        for k in range(j+1,N):
            cons.append(S[j,k]*O[j,k] >= 1 if A[j,k] else O[j,k] == 0)
    p = cp.Problem(cp.Minimize(w @ cp.diag(Q)), cons); p.solve(solver='SCS', eps=1e-7, max_iters=20000)
    return p.value, np.diag(Q.value)

def lp(q, I):
    # maximize sqrt3*(sum w - t) - w.q, sum w = 1, t >= I w
    N = len(q); c = np.concatenate([-(r3 - q), [r3]])
    Aub = np.hstack([I, -np.ones((len(I),1))]); bub = np.zeros(len(I))
    r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=[np.concatenate([np.ones(N),[0]])], b_eq=[1], bounds=[(0,None)]*N+[(None,None)], method='highs')
    return r.x[:N]

worst = (9, None)
for t in range(trials):
    A = np.triu((rng.random((N,N)) < pedge).astype(int), 1); A = A + A.T
    S = np.triu(rng.choice([-1,1], size=(N,N)), 1); S = S - S.T
    I = max_indep(A)
    w = rng.random(N)
    for it in range(8):
        val, q = sdp(w, A, S)
        alpha = max(I @ w); ratio = val/(w.sum() - alpha) if w.sum()-alpha > 1e-9 else 9
        if ratio < worst[0]: worst = (ratio, A.copy(), S.copy(), w.copy(), q.copy())
        w = lp(q, I)
print('N', N, 'trials', trials, 'p', pedge, 'min ratio F/(W-alpha) = %.5f   (sqrt3 = %.5f)' % (worst[0], r3))
print('A', worst[1].tolist()); print('S', worst[2].tolist()); print('w', np.round(worst[3],4).tolist()); print('q', np.round(worst[4],4).tolist())
