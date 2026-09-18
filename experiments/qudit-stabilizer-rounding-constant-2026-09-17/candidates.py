import numpy as np
from weyl import *

def ratio(c, mats, E):
    K = np.einsum('v,vij->ij', c, mats); assert np.allclose(K, K.conj().T)
    lam = np.linalg.eigvalsh(K)[-1]; s = np.max(np.real(E @ c)); W = np.sum(np.abs(c))
    return (lam - s) / (W - lam), lam, s, W

for d in [3, 5, 7, 11, 13]:
    vecs, mats = weyl_ops(d, 1); st = stabilizer_states(d, 1); E = expectations(st, mats)
    idx = {v: i for i, v in enumerate(vecs)}
    c = -np.ones(len(vecs)); r1 = ratio(c, mats, E)
    c = np.zeros(len(vecs), complex)
    for v in [(1, 0), (d - 1, 0), (0, 1), (0, d - 1)]: c[idx[v]] = 1
    r2 = ratio(c, mats, E)
    c = np.zeros(len(vecs), complex)
    for v in [(0, 1), (0, d - 1)] + [(1, a) for a in range(d)] + [(d - 1, (-a) % d) for a in range(d)]: c[idx[v]] = 1
    r3 = ratio(c, mats, E)
    print(d, "antiparity", np.round(r1, 4), d / ((d - 2) * (d + 1)), "harper", np.round(r2, 4), d / np.pi - 1, "all lines cos", np.round(r3, 4))
