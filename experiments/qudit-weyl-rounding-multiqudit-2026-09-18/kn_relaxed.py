# Relaxed complete-graph test: min ||Omega||_1 over real antisymmetric Omega with S_jk Omega_jk >= 1 (j<k),
# for random tournaments S; compare with sqrt3 (N-1) (the value needed for rho <= 4/sqrt3 at uniform weights).
import numpy as np, cvxpy as cp, sys
rng = np.random.default_rng(int(sys.argv[1]))
for N in range(3, int(sys.argv[2])+1):
    best = (1e9, None)
    for t in range(int(sys.argv[3])):
        S = np.triu(rng.choice([-1,1], size=(N,N)), 1); S = S - S.T
        if t == 0: S = np.sign(np.subtract.outer(np.arange(N), np.arange(N))).T  # transitive
        X = cp.Variable((N,N))
        cons = [X == -X.T] + [S[j,k]*X[j,k] >= 1 for j in range(N) for k in range(j+1,N)]
        p = cp.Problem(cp.Minimize(cp.normNuc(X)), cons); p.solve(solver='SCS', eps=1e-7, max_iters=20000)
        if p.value < best[0]: best = (p.value, S, X.value)
    print(N, 'min ||Om||_1 = %.5f' % best[0], ' sqrt3(N-1) = %.5f' % (np.sqrt(3)*(N-1)), ' ratio %.4f' % (best[0]/(N-1)), flush=True)
    if N <= 6: print(np.round(best[2], 3))
