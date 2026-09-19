"""numpy version of levels.py (same model, same recursion), for e >= 9.

An element of G_k is a row (s, h_0, ..., h_(M-1)) with s in Z/n and h_r ids in G_(k-1).
   g o b = (s, r -> h_r o d^(3^r mod n)),    g o d = (s+1, r -> h_(T r mod M) o b).
BFS by layers from the identity; rows are deduplicated through a 64-bit hash (two independent
hashes are compared at the end of each level as a collision check).
build(kmax) returns per level: sizes, and for the last level the tables Rb, Rd (numpy int64),
the rows, and pi: ids of the last level -> ids of the level before (natural projection).
usage: python3 levels_np.py e kmax
"""
import sys, math
import numpy as np
e = int(sys.argv[1]); kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
m = 2 ** e; n = m // 4; T = pow(3, -1, m)
M = max(2 ** (e - 4), 2)
pw = np.array([pow(3, r, n) for r in range(M)])
Tr = np.array([(T * r) % M for r in range(M)])
rng = np.random.default_rng(12345)
H1 = rng.integers(1, 2**63, size=M + 1, dtype=np.uint64) | np.uint64(1)
H2 = rng.integers(1, 2**63, size=M + 1, dtype=np.uint64) | np.uint64(1)

def hsh(rows, H):
    with np.errstate(over='ignore'):
        return (rows.astype(np.uint64) * H).sum(axis=1, dtype=np.uint64)

def powtab(R, v):
    """table of h -> h o d^v from R = table of h -> h o d, by binary powering."""
    out = np.arange(len(R)); P = R.copy()
    while v:
        if v & 1: out = P[out]
        v >>= 1
        if v: P = P[P]
    return out

def level(Rb, Rd):
    Rdv = {int(v): powtab(Rd, int(v)) for v in set(pw.tolist())}
    def kids(rows):
        s, h = rows[:, 0], rows[:, 1:]
        gb = np.empty_like(rows); gd = np.empty_like(rows)
        gb[:, 0] = s; gd[:, 0] = (s + 1) % n
        for r in range(M):
            gb[:, 1 + r] = Rdv[int(pw[r])][h[:, r]]
            gd[:, 1 + r] = Rb[h[:, Tr[r]]]
        return gb, gd
    one = np.zeros((1, M + 1), dtype=np.int64)
    allrows = [one]; seen = hsh(one, H1); front = one
    kb, kd = [], []
    while len(front):
        gb, gd = kids(front)
        hb, hd = hsh(gb, H1), hsh(gd, H1)
        kb.append(hb); kd.append(hd)
        cand = np.concatenate([gb, gd]); ch = np.concatenate([hb, hd])
        u, first = np.unique(ch, return_index=True)
        new = ~np.isin(u, seen)
        front = cand[first[new]]
        if len(front):
            allrows.append(front); seen = np.concatenate([seen, u[new]])
    rows = np.concatenate(allrows)
    order = np.argsort(seen); ss = seen[order]
    def ids(h): return order[np.searchsorted(ss, h)]
    nRb = ids(np.concatenate(kb)); nRd = ids(np.concatenate(kd))
    h2 = hsh(rows, H2)
    assert len(np.unique(h2)) == len(rows), "hash collision"
    return rows, nRb, nRd

def projection(Rb1, Rd1, Rb0, Rd0):
    """pi: G_(k) ids -> G_(k-1) ids, as a homomorphism along the Cayley graph."""
    pi = -np.ones(len(Rb1), dtype=np.int64); pi[0] = 0; front = np.array([0])
    while len(front):
        nxt = []
        for A1, A0 in ((Rb1, Rb0), (Rd1, Rd0)):
            c = A1[front]; v = A0[pi[front]]
            fresh = pi[c] < 0
            pi[c[fresh]] = v[fresh]; nxt.append(c[fresh])
        front = np.unique(np.concatenate(nxt))
    return pi

def build(kmax, verbose=True):
    Rb = np.zeros(1, dtype=np.int64); Rd = np.zeros(1, dtype=np.int64)
    sizes = []; rows = None; pi = None
    for k in range(1, kmax + 1):
        rows, nRb, nRd = level(Rb, Rd)
        pi = projection(nRb, nRd, Rb, Rd)
        Rb, Rd = nRb, nRd
        sizes.append(len(rows))
        if verbose: print("e=%d M=%d level %d: |G_k| = %d = 2^%.3f" % (e, M, k, len(rows), math.log2(len(rows))), flush=True)
    return Rb, Rd, rows, pi, sizes

if __name__ == '__main__':
    build(kmax)
