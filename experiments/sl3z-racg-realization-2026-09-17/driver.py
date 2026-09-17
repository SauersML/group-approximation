import sys, itertools, numpy as np
import antiflag as AF
from kernel import kernel_search


def calibrate():
    # (inf,inf,inf) Tits representation in GL_3(Z): faithful -> no kernel expected
    B = np.array([[1, -1, -1], [-1, 1, -1], [-1, -1, 1]])
    S = []
    for v in range(3):
        M = np.eye(3, dtype=np.int64)
        for w in range(3):
            M[v, w] -= 2 * B[v, w]
        S.append(M.T.copy())
    print("calib (inf,inf,inf) Tits:", kernel_search(3, [set(), set(), set()], S, max_len=12)[1:], "kernel:", kernel_search(3, [set(), set(), set()], S, max_len=12)[0][:1])
    # three reflections with common centre p=e3: relation expected at length <= 6
    verts = [((0, 0, 1), (0, 0, 1), 1), ((0, 0, 1), (1, 0, 1), 1), ((0, 0, 1), (0, 1, 1), 1)]
    S = [AF.reflection(x) for x in verts]
    print("calib common centre:", kernel_search(3, [set(), set(), set()], S, max_len=8))


def test_subgraph(verts, S_idx, A, max_len=6, max_elems=300000):
    idx = sorted(S_idx); pos = {v: i for i, v in enumerate(idx)}
    adjs = [set(pos[w] for w in A[v] if w in pos) for v in idx]
    mats = [AF.reflection(verts[v]) for v in idx]
    return kernel_search(len(idx), adjs, mats, max_len=max_len, max_elems=max_elems)


if __name__ == '__main__':
    calibrate()
