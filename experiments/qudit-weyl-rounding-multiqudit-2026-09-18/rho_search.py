# Semiclassical rounding ratio rho(Omega,w) = 4(W - m_iso)/||D Omega D||_1 over integer
# antisymmetric symplectic Gram matrices Omega (any such Omega is realised on enough qudits).
import numpy as np, itertools, sys
from scipy.optimize import minimize
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)

def indep_sets(Om):
    N = len(Om); res = []
    for mask in range(1, 1<<N):
        idx = [i for i in range(N) if mask>>i & 1]
        if all(Om[i,j]==0 for i in idx for j in idx if i<j):
            res.append(mask)
    # keep maximal
    mx = [s for s in res if not any((s|t)==t and s!=t for t in res)]
    return [np.array([(s>>i)&1 for i in range(N)], float) for s in mx]

def rho(w, Om, I):
    w = np.abs(w); W = w.sum()
    m = max(v@w for v in I)
    Dm = np.sqrt(w)
    s = np.linalg.svd(Dm[:,None]*Om*Dm[None,:], compute_uv=False).sum()
    return 4*(W-m)/s

def best(Om, tries=12):
    I = indep_sets(Om); N=len(Om); b=(0,None)
    for t in range(tries):
        x0 = rng.random(N)+0.1
        r = minimize(lambda x: -rho(x,Om,I), x0, method='Nelder-Mead', options={'maxiter':4000,'xatol':1e-9,'fatol':1e-12})
        if -r.fun > b[0]: b = (-r.fun, np.abs(r.x)/np.abs(r.x).sum())
    return b

if __name__ == '__main__':
    N = int(sys.argv[2]); vals = [int(v) for v in sys.argv[3].split(',')]; trials=int(sys.argv[4])
    top = []
    for t in range(trials):
        Om = np.zeros((N,N))
        for i in range(N):
            for j in range(i+1,N):
                Om[i,j] = rng.choice(vals); Om[j,i] = -Om[i,j]
        r,w = best(Om, 4)
        top.append((r, Om.astype(int).tolist(), None if w is None else np.round(w,4).tolist()))
    top.sort(key=lambda z:-z[0])
    print('N',N,'vals',vals,'trials',trials,'4/sqrt3=%.6f'%(4/np.sqrt(3)))
    for z in top[:5]: print('%.6f'%z[0], z[1], z[2])
