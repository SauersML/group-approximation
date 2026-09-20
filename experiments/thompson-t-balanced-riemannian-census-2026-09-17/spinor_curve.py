"""The spinor class in dimension 2 (A ~ {i,-i}, B ~ {w, w^2}) is a one-parameter family
up to conjugacy: A = i P - i (1-P), P = v v^*, v = (cos t/2, sin t/2), B = diag(w, w^2).
Scan D(t) on [0, pi] and list its local minima; the census attractors at n = 6, 24
are direct sums of copies sitting at one of these critical points.
"""
import json, math
import torch
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import CD, B_EIG, exact_defects


def pair(t):
    v = torch.tensor([math.cos(t / 2), math.sin(t / 2)], dtype=CD)
    P = torch.outer(v, v.conj())
    I2 = torch.eye(2, dtype=CD)
    return 1j * P - 1j * (I2 - P), torch.diag(torch.tensor([B_EIG[1], B_EIG[2]], dtype=CD))


N = 20000
ts = [math.pi * j / N for j in range(N + 1)]
Ds = [max(exact_defects(*pair(t))) for t in ts]
mins = [dict(t=ts[j], D=Ds[j], defects=exact_defects(*pair(ts[j])))
        for j in range(1, N) if Ds[j] <= Ds[j - 1] and Ds[j] <= Ds[j + 1]]
print(json.dumps(mins, indent=1))
json.dump(mins, open(__file__.rsplit('/', 1)[0] + '/out_spinor_curve.json', 'w'), indent=1)
