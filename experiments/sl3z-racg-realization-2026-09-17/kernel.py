"""Exact kernel search for an integral reflection representation rho: W_Gamma -> GL_3(Z).

Elements of W_Gamma are tracked faithfully by the contragredient Tits representation:
f -> s_v f, (s_v f)_w = f_w - 2 B(v,w) f_v with B(v,v)=1, B(v,w)=0 on edges, -1 on non-edges,
starting at f0 = (1,...,1) in the open fundamental chamber (trivial stabilizer).
Left-multiplying w by s increases length iff (w f0)_s > 0.
A kernel element is found when two different Tits vectors give the same 3x3 integer matrix.
"""
import numpy as np


def kernel_search(n, adjsets, S, max_len=8, max_elems=400000, want=1):
    Bm = -np.ones((n, n), dtype=np.int64)
    for v in range(n):
        Bm[v, v] = 1
        for w in adjsets[v]:
            Bm[v, w] = 0
    f0 = np.ones(n, dtype=np.int64)
    I = np.eye(3, dtype=np.int64)
    seen_tits = {f0.tobytes()}
    image = {I.tobytes(): (f0.tobytes(), ())}
    frontier = [(f0, I, ())]
    found = []
    total = 1
    for L in range(1, max_len + 1):
        new = []
        for f, M, word in frontier:
            for s in range(n):
                if f[s] <= 0:
                    continue
                g = f - 2 * Bm[s] * f[s]
                key = g.tobytes()
                if key in seen_tits:
                    continue
                seen_tits.add(key)
                N = S[s] @ M
                if np.abs(N).max() > 2 ** 40:
                    continue
                w2 = (s,) + word
                mk = N.tobytes()
                if mk in image:
                    found.append((image[mk][1], w2))
                    if len(found) >= want:
                        return found, L, total
                else:
                    image[mk] = (key, w2)
                new.append((g, N, w2))
                total += 1
                if total >= max_elems:
                    return found, L, total
        frontier = new
        if not new:
            break
    return found, max_len, total
