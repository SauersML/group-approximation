"""Planted control: spectra of k copies of the spinor class (A ~ {i,-i}, B ~ {w,w^2}).

The direct sum of k copies of the dimension-2 optimum has D = delta_2 = 0.3491491
(control_n2.py).  A random-start optimiser in dimension 2k must reach
D <= delta_2 + 0.01 to count as sighted at that dimension.
Usage: python3 control_planted.py k restarts steps
"""
import json, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import optimise

k, R, steps = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
mA = [0, k, 0, k]
mB = [0, k, k]
vals = []
for s in range(R):
    vals.append(optimise(mA, mB, seed=s, steps=steps)[0])
    print(2 * k, s, '%.5f' % vals[-1], flush=True)
rec = dict(n=2 * k, multA=mA, multB=mB, steps=steps, runs=vals, best=min(vals),
           sighted=min(vals) <= 0.3491491 + 0.01)
print(json.dumps(rec), flush=True)
json.dump(rec, open(__file__.rsplit('/', 1)[0] + '/out_control_planted_n%d.json' % (2 * k), 'w'), indent=1)
