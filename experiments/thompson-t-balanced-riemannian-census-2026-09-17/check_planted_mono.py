"""Local test at the planted direct sum (k copies of the dimension-2 optimum, D = 0.3491491).

(1) monotone polish from the planted point itself: can D be lowered below delta_2 locally?
(2) monotone polish from small random perturbations exp(s*skew) of the planted point,
    s in {0.05, 0.2, 0.5}: does the polish return to delta_2 (planted basin is attracting)?
Usage: python3 check_planted_mono.py k
"""
import json, sys
import torch
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import optimise, CD
from check_planted import planted

k = int(sys.argv[1])
A, B, U = planted(k)
mA, mB = [0, k, 0, k], [0, k, k]
gen = torch.Generator().manual_seed(11)
res = dict(k=k, n=2 * k)
D, _ = optimise(mA, mB, U0=U, steps=1000, lr=0.003, beta0=300.0, beta1=3000.0, monotone=True)
res['from_planted'] = D
print('k', k, 'monotone from planted %.6f' % D, flush=True)
res['perturbed'] = []
for s in [0.05, 0.2, 0.5]:
    for rep in range(2):
        n = 2 * k
        Z = (torch.randn(n, n, generator=gen) + 1j * torch.randn(n, n, generator=gen)).to(CD)
        S = (Z - Z.conj().T) * (s / (2 * n ** 0.5))
        U1 = U @ torch.linalg.matrix_exp(S)
        D1, _ = optimise(mA, mB, U0=U1, steps=1500, lr=0.01, beta0=100.0, beta1=3000.0, monotone=True)
        res['perturbed'].append(dict(s=s, D=D1))
        print('  s', s, 'rep', rep, 'D %.6f' % D1, flush=True)
json.dump(res, open(__file__.rsplit('/', 1)[0] + '/out_planted_mono_k%d.json' % k, 'w'), indent=1)
