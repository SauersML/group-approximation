"""Resumable version of levels_np.py (same model, same layered BFS), for e >= 9 on a loaded machine.

State is checkpointed in ck<e>/ after every BFS layer once a wall-clock budget is used up, and after
every level; re-running continues where it stopped (exit code 3 = budget used, run again).
Level k is stored as ck<e>/L<k>.npz with Rb, Rd (int32 tables h -> h o b, h -> h o d), the rows
(s, h_0..h_(M-1)) and pi (ids of level k -> ids of level k-1).
usage: python3 levels_ck.py e kmax [budget_seconds]
"""
import sys, os, math, time
import numpy as np
e = int(sys.argv[1]); kmax = int(sys.argv[2]); budget = float(sys.argv[3]) if len(sys.argv) > 3 else 900
t0 = time.time()
m = 2 ** e; n = m // 4; T = pow(3, -1, m)
M = max(2 ** (e - 4), 2)
pw = np.array([pow(3, r, n) for r in range(M)])
Tr = np.array([(T * r) % M for r in range(M)])
rng = np.random.default_rng(12345)
H1 = rng.integers(1, 2**63, size=M + 1, dtype=np.uint64) | np.uint64(1)
H2 = rng.integers(1, 2**63, size=M + 1, dtype=np.uint64) | np.uint64(1)
CK = 'ck%d' % e
os.makedirs(CK, exist_ok=True)

def hsh(rows, H):
    out = np.zeros(len(rows), dtype=np.uint64)
    with np.errstate(over='ignore'):
        for j in range(rows.shape[1]):
            out += rows[:, j].astype(np.uint64) * H[j]
    return out

def powtab(R, v):
    out = np.arange(len(R), dtype=np.int32); P = R.copy()
    while v:
        if v & 1: out = P[out]
        v >>= 1
        if v: P = P[P]
    return out

def level(k, Rb, Rd):
    Rdv = {int(v): powtab(Rd, int(v)) for v in set(pw.tolist())}
    def kids(rows):
        s, h = rows[:, 0], rows[:, 1:]
        gb = np.empty_like(rows); gd = np.empty_like(rows)
        gb[:, 0] = s; gd[:, 0] = (s + 1) % n
        for r in range(M):
            gb[:, 1 + r] = Rdv[int(pw[r])][h[:, r]]
            gd[:, 1 + r] = Rb[h[:, Tr[r]]]
        return gb, gd
    st = os.path.join(CK, 'bfs%d.npz' % k)
    if os.path.exists(st):
        z = np.load(st); rows = z['rows']; seen = z['seen']; kb = [z['kb']]; kd = [z['kd']]
        front = rows[int(z['start']):]
        allrows = [rows]
    else:
        one = np.zeros((1, M + 1), dtype=np.int32)
        allrows = [one]; seen = hsh(one, H1); front = one; kb, kd = [], []
    start = sum(len(x) for x in allrows) - len(front)
    while len(front):
        if kb and time.time() - t0 > budget:
            rows = np.concatenate(allrows)
            np.savez(st + '.tmp.npz', rows=rows, seen=seen, kb=np.concatenate(kb), kd=np.concatenate(kd), start=start)
            os.replace(st + '.tmp.npz', st)
            print("budget used in level %d at %d rows; checkpointed" % (k, len(rows)), flush=True)
            sys.exit(3)
        gb, gd = kids(front)
        hb, hd = hsh(gb, H1), hsh(gd, H1)
        kb.append(hb); kd.append(hd)
        cand = np.concatenate([gb, gd]); ch = np.concatenate([hb, hd]); del gb, gd
        u, first = np.unique(ch, return_index=True)
        new = ~np.isin(u, seen)
        start = sum(len(x) for x in allrows)
        front = cand[first[new]]; del cand
        if len(front):
            allrows.append(front); seen = np.concatenate([seen, u[new]])
    rows = np.concatenate(allrows); del allrows
    order = np.argsort(seen); ss = seen[order]
    def ids(h): return order[np.searchsorted(ss, h)].astype(np.int32)
    nRb = ids(np.concatenate(kb)); nRd = ids(np.concatenate(kd))
    assert len(np.unique(hsh(rows, H2))) == len(rows), "hash collision"
    return rows, nRb, nRd

def projection(Rb1, Rd1, Rb0, Rd0):
    pi = -np.ones(len(Rb1), dtype=np.int32); pi[0] = 0; front = np.array([0])
    while len(front):
        nxt = []
        for A1, A0 in ((Rb1, Rb0), (Rd1, Rd0)):
            c = A1[front]; v = A0[pi[front]]
            fresh = pi[c] < 0
            pi[c[fresh]] = v[fresh]; nxt.append(c[fresh])
        front = np.unique(np.concatenate(nxt))
    return pi

def load(k):
    z = np.load(os.path.join(CK, 'L%d.npz' % k)); return z['Rb'], z['Rd'], z['rows'], z['pi']

if __name__ == '__main__':
    Rb = np.zeros(1, dtype=np.int32); Rd = np.zeros(1, dtype=np.int32)
    have = [k for k in range(1, kmax + 1) if os.path.exists(os.path.join(CK, 'L%d.npz' % k))]
    k0 = max(have) if have else 1
    prev = None
    if k0 > 1 and os.path.exists(os.path.join(CK, 'L%d.npz' % (k0 - 1))):
        prev = len(np.load(os.path.join(CK, 'L%d.npz' % (k0 - 1)))['Rb'])
    for k in range(k0, kmax + 1):
        f = os.path.join(CK, 'L%d.npz' % k)
        if os.path.exists(f):
            z = np.load(f); Rb1, Rd1 = z['Rb'], z['Rd']; rows = Rb1   # rows not needed to go on
        else:
            rows, Rb1, Rd1 = level(k, Rb, Rd)
            pi = projection(Rb1, Rd1, Rb, Rd)
            np.savez(f + '.tmp.npz', Rb=Rb1, Rd=Rd1, rows=rows, pi=pi); os.replace(f + '.tmp.npz', f)
            b = os.path.join(CK, 'bfs%d.npz' % k)
            if os.path.exists(b): os.remove(b)
            if k >= 3 and os.path.exists(os.path.join(CK, 'L%d.npz' % (k - 2))):
                os.remove(os.path.join(CK, 'L%d.npz' % (k - 2)))   # keep only the last two levels
        Rb, Rd = Rb1, Rd1
        N = len(rows); del rows
        print("e=%d M=%d level %d: |G_k| = %d = 2^%.3f  (t=%.0fs)" % (e, M, k, N, math.log2(N), time.time() - t0), flush=True)
        if prev == N:
            print("stable: |G_%d| = |G_%d|, so Bbar_%d = G_%d (stabilization lemma)" % (k - 1, k, e, k), flush=True)
            break
        prev = N
