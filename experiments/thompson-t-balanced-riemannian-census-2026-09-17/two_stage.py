"""Two-stage search: non-monotone annealed exploration, then monotone polish, then
monotone basin hopping (perturb exp(s*skew), polish, accept if better).

Usage: python3 two_stage.py <tag> <multA comma> <multB comma> <starts> <hops> <steps> [seed0]
Writes out_two_stage_<tag>.json and saves the best U to the scratchpad.
"""
import json, sys, time
import torch
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import optimise, CD, pair_from_U, diag_from_mult, exact_defects, A_EIG, B_EIG

SCR = '/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad'


def polish(mA, mB, U, steps):
    return optimise(mA, mB, U0=U, steps=steps, lr=0.01, beta0=100.0, beta1=3000.0, monotone=True)


def perturb(U, s, gen):
    n = U.shape[0]
    Z = (torch.randn(n, n, generator=gen) + 1j * torch.randn(n, n, generator=gen)).to(CD)
    S = (Z - Z.conj().T) * (s / (2 * n ** 0.5))
    return U @ torch.linalg.matrix_exp(S)


def run(tag, mA, mB, starts, hops, steps, seed0=0):
    gen = torch.Generator().manual_seed(seed0 + 17)
    best = (9.0, None)
    trace = []
    for st in range(starts):
        D0, U = optimise(mA, mB, seed=seed0 + st, steps=steps)
        D, U = polish(mA, mB, U, steps)
        path = [D0, D]
        for h in range(hops):
            s = [0.3, 0.8, 1.5][h % 3]
            D2, U2 = polish(mA, mB, perturb(U, s, gen), steps)
            if D2 < D:
                D, U = D2, U2
            path.append(D)
        trace.append(path)
        print(tag, 'start', st, ' '.join('%.5f' % x for x in path), flush=True)
        if D < best[0]:
            best = (D, U)
    return best, trace


if __name__ == '__main__':
    tag = sys.argv[1]
    mA = [int(x) for x in sys.argv[2].split(',')]
    mB = [int(x) for x in sys.argv[3].split(',')]
    starts, hops, steps = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    seed0 = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    t0 = time.time()
    (D, U), trace = run(tag, mA, mB, starts, hops, steps, seed0=seed0)
    A, B = pair_from_U(U, diag_from_mult(A_EIG, mA), diag_from_mult(B_EIG, mB))
    rec = dict(tag=tag, n=sum(mA), multA=mA, multB=mB, best=D, defects=exact_defects(A, B),
               trace=trace, seconds=time.time() - t0)
    print(json.dumps(rec), flush=True)
    json.dump(rec, open(__file__.rsplit('/', 1)[0] + '/out_two_stage_%s.json' % tag, 'w'), indent=1)
    torch.save(U, SCR + '/U2_%s.pt' % tag)
