# sl2link.py -- the coset graph Gamma(SL_2(F_N); u(L), v(L')) for additive subgroups L, L' of F_N, N = 2^n.
#   u(x) = [[1,x],[0,1]], v(y) = [[1,0],[y,1]]; E = u(L), E' = v(L').
# Side 1 = SL_2/E, side 2 = SL_2/E', one edge per group element g (joining gE and gE').
# Reports: vertex counts and degrees, connectivity (= <E,E'> = SL_2(F_N)), girth from a base vertex
# (the graph is vertex-transitive on each side and every cycle meets side 1), numerical top singular
# values of the normalized biadjacency, and exact closed-walk counts W_{2m} from the base vertex
# (multi-modular, CRT), which give the rigorous bound  sigma_2^{2m} <= n1 * W_{2m} / (|L|^m |L'|^m) - 1.
# Usage: sage -python sl2link.py n f s_exp mmax [theta_num theta_den]
#   n = log2 N; f: L = F_{2^f} (subfield, f | n); L' = s*L with s = g^s_exp (g the primitive element found);
#   s_exp = -1 means L' = L (root subgroups when f = n).
import sys, time, math, json
import numpy as np, scipy.sparse as sp
from scipy.sparse.linalg import eigsh, LinearOperator
from scipy.sparse.csgraph import connected_components

def field(n):
    N = 1 << n
    for poly in range(N + 1, 2 * N, 2):
        exp = np.zeros(2 * N, dtype=np.int64); x = 1; seen = set(); ok = True
        for i in range(N - 1):
            if x in seen: ok = False; break
            seen.add(x); exp[i] = x
            x <<= 1
            if x & N: x ^= poly
        if ok and x == 1 and len(seen) == N - 1:
            exp[N - 1:2 * N - 1] = exp[0:N]
            log = np.zeros(N, dtype=np.int64)
            log[exp[:N - 1]] = np.arange(N - 1)
            return poly, exp, log
    raise ValueError("no primitive polynomial")

n, f, s_exp, mmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
theta = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else None
N = 1 << n
poly, EXP, LOG = field(n)
def mul(a, b):
    a = np.asarray(a, dtype=np.int64); b = np.asarray(b, dtype=np.int64)
    r = EXP[LOG[a] + LOG[b]]
    return np.where((a == 0) | (b == 0), 0, r)
def inv(a):
    a = np.asarray(a, dtype=np.int64)
    return np.where(a == 0, -1, EXP[(N - 1) - LOG[a]])
def powe(a, e):
    r = 1
    for _ in range(e): r = int(mul(r, a))
    return r

allF = np.arange(N, dtype=np.int64)
L = np.array([a for a in range(N) if powe(a, 1 << f) == a], dtype=np.int64)   # subfield F_{2^f}
assert len(L) == (1 << f)
s = -1 if s_exp < 0 else int(EXP[s_exp])
Lp = L.copy() if s < 0 else np.sort(mul(s, L))
if s >= 0: assert len(set(Lp.tolist()) & set(L.tolist())) == 1, "s must lie outside F_{2^f}"
def classes(sub):
    rep = np.array([min(int(t) ^ int(x) for x in sub) for t in range(N)], dtype=np.int64)
    reps = np.unique(rep); idx = -np.ones(N, dtype=np.int64); idx[reps] = np.arange(len(reps))
    return idx[rep], reps
cls1, reps1 = classes(L); cls2, reps2 = classes(Lp)
nc1, nc2 = len(reps1), len(reps2)
n1, n2 = (N * N - 1) * nc1, (N * N - 1) * nc2
print("N=%d poly=%s f=%d s=%d |L|=%d n1=%d n2=%d" % (N, bin(poly), f, s, len(L), n1, n2), flush=True)

t0 = time.time()
V = np.arange(1, N * N, dtype=np.int64); A_, C_ = V // N, V % N            # v = (a, c) != 0
aa = np.repeat(A_, nc1 * len(L)); cc = np.repeat(C_, nc1 * len(L))
vid = np.repeat(V - 1, nc1 * len(L))
tt = np.tile(np.repeat(reps1, len(L)) ^ np.tile(L, nc1), N * N - 1)
w0b = np.where(aa != 0, 0, inv(cc)); w0d = np.where(aa != 0, inv(aa), 0)
bb = w0b ^ mul(tt, aa); dd = w0d ^ mul(tt, cc)
assert np.all((mul(aa, dd) ^ mul(bb, cc)) == 1)
row = vid * nc1 + cls1[np.where(aa != 0, mul(bb, inv(aa)), mul(dd ^ w0d, inv(cc)))]
tp = np.where(dd != 0, mul(cc, inv(dd)), mul(aa, inv(bb)))
col = (bb * N + dd - 1) * nc2 + cls2[tp]
M = sp.csr_matrix((np.ones(len(row), dtype=np.int64), (row, col)), shape=(n1, n2))
M.sum_duplicates()
deg1 = np.diff(M.indptr); deg2 = np.bincount(M.indices, minlength=n2)
print("edges=%d maxentry=%d deg1 in [%d,%d] deg2 in [%d,%d] build %.1fs" % (M.nnz, M.data.max(), deg1.min(), deg1.max(), deg2.min(), deg2.max(), time.time() - t0), flush=True)
assert M.data.max() == 1 and deg1.min() == deg1.max() == len(L) and deg2.min() == deg2.max() == len(Lp)

Adj = sp.bmat([[None, M], [M.T, None]]).tocsr()
ncomp, _ = connected_components(Adj, directed=False)
print("components=%d" % ncomp, flush=True)

# girth through side-1 vertex 0 (layered BFS)
dist = -np.ones(n1 + n2, dtype=np.int64); par = -np.ones(n1 + n2, dtype=np.int64)
dist[0] = 0; front = np.array([0]); best = 10 ** 9; lev = 0
while len(front) and 2 * lev + 1 < best:
    starts = np.repeat(front, np.diff(Adj.indptr)[front])
    ends = np.concatenate([Adj.indices[Adj.indptr[u]:Adj.indptr[u + 1]] for u in front])
    keep = ends != par[starts]; starts, ends = starts[keep], ends[keep]
    seen = dist[ends] >= 0
    if seen.any(): best = min(best, int((dist[starts[seen]] + dist[ends[seen]] + 1).min()))
    new_s, new_e = starts[~seen], ends[~seen]
    uq, first, cnt = np.unique(new_e, return_index=True, return_counts=True)
    if (cnt > 1).any(): best = min(best, 2 * (lev + 1))
    dist[uq] = lev + 1; par[uq] = new_s[first]; front = uq; lev += 1
print("girth=%d" % best, flush=True)

qL, qLp = len(L), len(Lp)
Mf = M.astype(np.float64)
op = LinearOperator((n1, n1), matvec=lambda x: Mf @ (Mf.T @ x) / (qL * qLp), dtype=np.float64)
t0 = time.time()
vals = np.sort(eigsh(op, k=6, which="LA", tol=1e-10, maxiter=5000, return_eigenvectors=False))[::-1]
print("top singular values:", " ".join("%.6f" % math.sqrt(max(v, 0)) for v in vals), "(%.1fs)" % (time.time() - t0), flush=True)

def is_prime(m):
    if m < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % p == 0: return m == p
    d, r = m - 1, 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        x = pow(a, d, m)
        if x in (0, 1, m - 1): continue
        for _ in range(r - 1):
            x = pow(x, 2, m)
            if x == m - 1: break
        else: return False
    return True
bits = mmax * math.log2(max(qL, qLp)) + math.log2(n1) + 8
primes = []; cand = (1 << 57) - 1
while len(primes) * 56 < bits:
    if is_prime(cand): primes.append(cand)
    cand -= 2
P = np.array(primes, dtype=np.int64)
t0 = time.time()
vec = np.zeros((n1, len(P)), dtype=np.int64); vec[0, :] = 1
Mi, MTi = M, M.T.tocsr()
W = {}
for m in range(1, mmax // 2 + 1):
    vec = (MTi @ vec) % P
    vec = (Mi @ vec) % P
    residues = [int(r) for r in vec[0]]
    x, mod = 0, 1
    for r, p in zip(residues, primes):                                   # CRT
        k = ((r - x) * pow(mod, -1, p)) % p
        x, mod = x + mod * k, mod * p
    W[2 * m] = x
print("walks to length %d in %.1fs with %d primes" % (mmax, time.time() - t0, len(P)), flush=True)
out = []
for tm, w in sorted(W.items()):
    m = tm // 2
    X = n1 * w - qL ** m * qLp ** m
    assert X >= 0 and w <= qL ** m * qLp ** m
    bound = math.exp((math.log(X) - m * math.log(qL * qLp)) / tm) if X > 0 else 0.0
    cert = None
    if theta:
        a, b = theta
        cert = X * b ** tm < a ** tm * qL ** m * qLp ** m
    out.append((tm, bound, cert))
for tm, bound, cert in out:
    if tm <= 12 or tm % 20 == 0 or tm == mmax:
        print("2m=%d  W=%d  sigma2 <= %.6f  cert(theta=%s)=%s" % (tm, W[tm], bound, theta, cert))
certs = [tm for tm, b, c in out if c]
print("first certifying 2m:", certs[0] if certs else None)
print("DONE")
