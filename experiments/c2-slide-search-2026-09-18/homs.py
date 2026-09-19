# Fast vectorised count of homomorphisms <t,x,y | R0,R1> -> Q with t != 1, for small permutation groups Q.
# x runs over conjugacy-class representatives, y and t over all of Q.
import numpy as np
def perm_group(gens, n):
    e = tuple(range(n)); S = {e}; fr = [e]
    while fr:
        new = []
        for a in fr:
            for g in gens:
                b = tuple(g[a[k]] for k in range(n))
                if b not in S: S.add(b); new.append(b)
        fr = new
    P = sorted(S); idx = {p: i for i, p in enumerate(P)}
    mul = np.array([[idx[tuple(a[b[k]] for k in range(n))] for b in P] for a in P], dtype=np.int32)  # a∘b
    inv = np.array([idx[tuple(sorted(range(n), key=lambda k: a[k]))] for a in P], dtype=np.int32)
    ei = idx[e]
    reps, seen = [], set()
    for a in range(len(P)):
        if a in seen: continue
        reps.append(a)
        for b in range(len(P)): seen.add(int(mul[mul[b][a]][inv[b]]))
    return dict(P=P, mul=mul, inv=inv, e=ei, reps=reps)
def pgl2(p):
    # PGL(2,p) acting on the projective line {0..p-1, inf=p}
    def mob(a, b, c, d):
        out = []
        for z in range(p + 1):
            if z == p: num, den = a, c
            else: num, den = (a * z + b) % p, (c * z + d) % p
            out.append(p if den == 0 else num * pow(den, -1, p) % p)
        return tuple(out)
    nsq = min(a for a in range(2, p) if pow(a, (p - 1) // 2, p) == p - 1)
    return [mob(1, 1, 0, 1), mob(0, p - 1, 1, 0), mob(nsq, 0, 0, 1)]
def psl2(p):
    def mob(a, b, c, d):
        out = []
        for z in range(p + 1):
            if z == p: num, den = a, c
            else: num, den = (a * z + b) % p, (c * z + d) % p
            out.append(p if den == 0 else num * pow(den, -1, p) % p)
        return tuple(out)
    return [mob(1, 1, 0, 1), mob(0, p - 1, 1, 0)]
GROUPS = {
    'A5': ([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)], 5),
    'S5': ([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)], 5),
    'PSL27': (psl2(7), 8),
    'A6': ([(1, 2, 0, 3, 4, 5), (0, 2, 3, 4, 5, 1)], 6),
    'PGL27': (pgl2(7), 8),
    'PSL211': (psl2(11), 12),
    'S6': ([(1, 0, 2, 3, 4, 5), (1, 2, 3, 4, 5, 0)], 6),
    'PSL213': (psl2(13), 14),
    'A7': ([(1, 2, 0, 3, 4, 5, 6), (0, 1, 3, 4, 5, 6, 2)], 7),
}
_cache = {}
def group(name):
    if name not in _cache: _cache[name] = perm_group(*GROUPS[name])
    return _cache[name]
def evalw(word, Q, X, Y, T):
    mul, inv = Q['mul'], Q['inv']
    im = {'x': X, 'X': inv[X], 'y': Y, 'Y': inv[Y], 't': T, 'T': inv[T]}
    g = np.full(X.shape, Q['e'], dtype=np.int32)
    for c in word: g = mul[g, im[c]]
    return g
def count(R0, R1, name, limit=None):
    """number of (x class rep, y, t) with t != 1 satisfying R0 = R1 = 1; returns (count, example)."""
    Q = group(name); N = len(Q['P'])
    ts = np.array([i for i in range(N) if i != Q['e']], dtype=np.int32)
    tot, ex = 0, None
    for xr in Q['reps']:
        Y, T = np.meshgrid(np.arange(N, dtype=np.int32), ts, indexing='ij')
        Y = Y.ravel(); T = T.ravel(); X = np.full(Y.shape, xr, dtype=np.int32)
        ok = evalw(R0, Q, X, Y, T) == Q['e']
        X, Y, T = X[ok], Y[ok], T[ok]
        if len(X) == 0: continue
        ok = evalw(R1, Q, X, Y, T) == Q['e']
        k = int(ok.sum()); tot += k
        if k and ex is None: ex = (int(T[ok][0]), int(X[ok][0]), int(Y[ok][0]))
        if limit and tot >= limit: break
    return tot, ex
if __name__ == '__main__':
    import sys, os, time
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from slide import build
    from verify_unimodular import D
    for z0 in 'cb':
        R0, R1 = build(D, z0)
        for nm in GROUPS:
            t0 = time.time(); print(z0, nm, len(group(nm)['P']), count(R0, R1, nm), round(time.time() - t0, 1), flush=True)
