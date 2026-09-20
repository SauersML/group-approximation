"""Control: in dimension 2 the pair space mod conjugation is one real parameter.

B = diag(w, w^2), A = i(2 v v^* - 1), v = (cos(t/2), sin(t/2)); the diagonal torus
commuting with B removes the phase of v_2.  Brute force over t gives the exact
minimum of D for the spinor spectra A ~ {i,-i}, B ~ {w,w^2}; the optimiser must match it.
Also scans every 2-dimensional spectral class with A != 1.
"""
import itertools, json, math, sys
import torch
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import CD, A_EIG, B_EIG, exact_defects, optimise


def brute(ea, eb, N=20001):
    best = (9.0, None)
    for k in range(N):
        t = math.pi * k / (N - 1)
        v = torch.tensor([math.cos(t / 2), math.sin(t / 2)], dtype=CD)
        P = torch.outer(v, v.conj())
        I = torch.eye(2, dtype=CD)
        A = ea[0] * P + ea[1] * (I - P)
        B = torch.diag(torch.tensor(eb, dtype=CD))
        D = max(exact_defects(A, B))
        if D < best[0]:
            best = (D, t)
    return best


out = []
idxA = list(itertools.combinations_with_replacement(range(4), 2))
idxB = list(itertools.combinations_with_replacement(range(3), 2))
for ia in idxA:
    if ia == (0, 0):
        continue
    for ib in idxB:
        ea = [A_EIG[j] for j in ia]
        eb = [B_EIG[j] for j in ib]
        bD, bt = brute(ea, eb, 4001)
        mA = [ia.count(j) for j in range(4)]
        mB = [ib.count(j) for j in range(3)]
        oD = min(optimise(mA, mB, seed=s, steps=800)[0] for s in range(4))
        out.append(dict(multA=mA, multB=mB, brute=bD, theta=bt, optimiser=oD))
        print(mA, mB, 'brute %.6f  opt %.6f' % (bD, oD), flush=True)
json.dump(out, open(__file__.rsplit('/', 1)[0] + '/out_control_n2.json', 'w'), indent=1)
print('global min over nontrivial 2-dim classes:', min(o['brute'] for o in out))
