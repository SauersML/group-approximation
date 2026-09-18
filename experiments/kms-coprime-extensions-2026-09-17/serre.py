"""Serre algebra n(A) for the HC1 matrix (a_ab=a_ba=a_bc=a_cb=a_ac=-1, a_ca=-2).
U(n) = free assoc algebra on e_a,e_b,e_c / Serre ideal.  For bidegree (i,j), compute the
rank of the span of all Lie monomials in x=[e_b,e_a], y=[e_b,e_c] with i x's and j y's,
inside U(n) in multidegree (i, i+j, j), over F_q."""
import itertools, sys
import numpy as np

q = int(sys.argv[1]); maxdeg = int(sys.argv[2])

def mul(P, Q):
    out = {}
    for u, cu in P.items():
        for v, cv in Q.items():
            w = u + v
            out[w] = (out.get(w, 0) + cu * cv) % q
    return {k: v for k, v in out.items() if v}

def add(P, Q, s=1):
    out = dict(P)
    for k, v in Q.items():
        out[k] = (out.get(k, 0) + s * v) % q
    return {k: v for k, v in out.items() if v}

def br(P, Q):
    return add(mul(P, Q), mul(Q, P), -1)

E = {g: {(g,): 1} for g in range(3)}  # 0=a,1=b,2=c
def adpow(x, k, y):
    for _ in range(k):
        y = br(x, y)
    return y
rels = [adpow(E[0], 2, E[1]), adpow(E[1], 2, E[0]), adpow(E[1], 2, E[2]), adpow(E[2], 2, E[1]),
        adpow(E[0], 2, E[2]), adpow(E[2], 3, E[0]), br(E[0], br(E[2], br(E[2], E[0])))]

def mdeg(word):
    d = [0, 0, 0]
    for g in word:
        d[g] += 1
    return tuple(d)

def words_of(d):
    base = [0] * d[0] + [1] * d[1] + [2] * d[2]
    return sorted(set(itertools.permutations(base)))

def ideal_rank_and_reduce(d, targets):
    ws = words_of(d)
    idx = {w: k for k, w in enumerate(ws)}
    rows = []
    for R in rels:
        rd = mdeg(next(iter(R)))
        rem = tuple(x - y for x, y in zip(d, rd))
        if min(rem) < 0:
            continue
        L = sum(rem)
        base = [0] * rem[0] + [1] * rem[1] + [2] * rem[2]
        for perm in set(itertools.permutations(base)):
            for cut in range(L + 1):
                u, v = perm[:cut], perm[cut:]
                row = {}
                for w, cf in R.items():
                    row[idx[u + w + v]] = cf
                rows.append(row)
    n = len(ws)
    M = np.zeros((len(rows), n), dtype=np.int64)
    for k, row in enumerate(rows):
        for j, cf in row.items():
            M[k, j] = cf
    T = np.zeros((len(targets), n), dtype=np.int64)
    for k, P in enumerate(targets):
        for w, cf in P.items():
            T[k, idx[w]] = cf
    return n, rank(M), rank(np.concatenate([M, T]))

def rank(M):
    M = M.copy() % q
    r = 0
    rows, cols = M.shape
    for col in range(cols):
        if r >= rows: break
        nz = np.nonzero(M[r:, col])[0]
        if len(nz) == 0: continue
        piv = r + nz[0]
        M[[r, piv]] = M[[piv, r]]
        M[r] = (M[r] * pow(int(M[r, col]), q - 2, q)) % q
        f = M[:, col].copy(); f[r] = 0
        nzr = np.nonzero(f)[0]
        if len(nzr): M[nzr] = (M[nzr] - np.outer(f[nzr], M[r])) % q
        r += 1
    return r

x = br(E[1], E[0]); y = br(E[1], E[2])
for k in range(2, maxdeg + 1):
    for i in range(1, k):
        j = k - i
        # all right-normed Lie monomials in x,y with i x's, j y's
        mons = []
        for seq in set(itertools.permutations([0] * i + [1] * j)):
            P = x if seq[-1] == 0 else y
            for s in reversed(seq[:-1]):
                P = br(x if s == 0 else y, P)
            if P: mons.append(P)
        d = (i, i + j, j)
        n, ri, rt = ideal_rank_and_reduce(d, mons)
        print(f"q={q} bidegree (x^{i},y^{j}) multideg {d}: words {n}, ideal rank {ri}, Lie span dim mod ideal {rt-ri}", flush=True)
