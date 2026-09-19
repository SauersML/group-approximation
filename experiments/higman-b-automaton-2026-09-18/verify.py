"""Exact verification of one level of levels_ck.py (no hashing): the rows of level k are pairwise
distinct, row 0 is the identity, and the tables Rb, Rd of level k agree exactly with the recursion
    g o b = (s, r -> h_r o d^(3^r)),   g o d = (s+1, r -> h_(T r mod M) o b)
evaluated with the (already verified) tables of level k-1. Then the rows are exactly the finite
set {1} closed under o b and o d, i.e. G_k, and |G_k| = number of rows. Level 1 is checked against
the trivial group (level 0).
usage: python3 verify.py e k fileLk [fileLk-1]
"""
import sys
import numpy as np
e, k = int(sys.argv[1]), int(sys.argv[2])
m = 2 ** e; n = m // 4; M = max(2 ** (e - 4), 2); T = pow(3, -1, m)
z1 = np.load(sys.argv[3]); Rb, Rd, rows = z1['Rb'], z1['Rd'], z1['rows']
if k == 1: Rb0 = np.zeros(1, dtype=np.int64); Rd0 = np.zeros(1, dtype=np.int64)
else: z0 = np.load(sys.argv[4]); Rb0, Rd0 = z0['Rb'], z0['Rd']
pw = [pow(3, r, n) for r in range(M)]; Tr = [(T * r) % M for r in range(M)]
def dpow(v):
    out = np.arange(len(Rd0)); P = Rd0.copy()
    while v:
        if v & 1: out = P[out]
        v >>= 1
        if v: P = P[P]
    return out
Dv = {v: dpow(v) for v in set(pw)}
ok = bool((rows[0] == 0).all())
ok &= bool((rows[Rb, 0] == rows[:, 0]).all()) and bool((rows[Rd, 0] == (rows[:, 0] + 1) % n).all())
for r in range(M):
    ok &= bool((rows[Rb, 1 + r] == Dv[pw[r]][rows[:, 1 + r]]).all())
    ok &= bool((rows[Rd, 1 + r] == Rb0[rows[:, 1 + Tr[r]]]).all())
srt = np.lexsort(rows.T[::-1]); dif = (rows[srt[1:]] != rows[srt[:-1]]).any(axis=1)
ok &= bool(dif.all())
print("e=%d level %d: %d rows, exact verification %s" % (e, k, len(rows), "OK" if ok else "FAILED"))
