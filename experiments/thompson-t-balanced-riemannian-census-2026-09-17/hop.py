"""Basin-hopping wrapper around census.optimise.

Each hop perturbs the incumbent U by exp(s * random skew-Hermitian), s in {0.3, 1.0},
re-optimises with a short annealing schedule restarted at moderate beta, and keeps
the better pair.  Usage:
  python3 hop.py <tag> <multA comma> <multB comma> <starts> <hops> <steps>
"""
import json, sys, time
import torch
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import optimise, CD


def perturb(U, s, gen):
    n = U.shape[0]
    Z = torch.randn(n, n, generator=gen) + 1j * torch.randn(n, n, generator=gen)
    Z = Z.to(CD)
    S = (Z - Z.conj().T) * (s / (2 * n ** 0.5))
    return U @ torch.linalg.matrix_exp(S)


def run(mA, mB, starts, hops, steps, seed0=0):
    gen = torch.Generator().manual_seed(seed0 + 7)
    best_all = (9.0, None)
    trace = []
    for st in range(starts):
        D, U = optimise(mA, mB, seed=seed0 + st, steps=steps)
        path = [D]
        for h in range(hops):
            s = [0.3, 1.0][h % 2]
            D2, U2 = optimise(mA, mB, seed=0, steps=steps // 2, U0=perturb(U, s, gen), beta0=30.0)
            if D2 < D:
                D, U = D2, U2
            path.append(D)
        trace.append(path)
        if D < best_all[0]:
            best_all = (D, U)
    return best_all, trace


if __name__ == '__main__':
    tag = sys.argv[1]
    mA = [int(x) for x in sys.argv[2].split(',')]
    mB = [int(x) for x in sys.argv[3].split(',')]
    starts, hops, steps = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    t0 = time.time()
    (D, U), trace = run(mA, mB, starts, hops, steps)
    rec = dict(tag=tag, n=sum(mA), multA=mA, multB=mB, best=D, trace=trace, seconds=time.time() - t0)
    print(json.dumps(rec), flush=True)
    json.dump(rec, open(__file__.rsplit('/', 1)[0] + '/out_hop_%s.json' % tag, 'w'), indent=1)
    torch.save(U, '/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad/U_%s.pt' % tag)
