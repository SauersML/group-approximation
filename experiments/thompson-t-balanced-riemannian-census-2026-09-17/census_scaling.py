"""Scaling census: minimum operator-norm defect D over exact Z/4*Z/3 pairs with the
T-line spectra of the spectral-balance lemma, dimensions n = 12k.

For every best pair we also record
  * commutant dimension of (A,B) at tolerance 1e-5 (1 = irreducible),
  * the three individual relator defects,
  * normalised traces of B A and of (B A)^5 (spectral-balance diagnostics).
Usage: python3 census_scaling.py <tag> <a> <k1,k2,...> <restarts> <steps>
"""
import json, sys, time
import torch
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from census import optimise, spectra_balanced, pair_from_U, diag_from_mult, exact_defects, A_EIG, B_EIG, CD


def commutant_dim(A, B, tol=1e-5):
    n = A.shape[0]
    I = torch.eye(n, dtype=CD)
    LA = torch.kron(A, I) - torch.kron(I, A.T.contiguous())
    LB = torch.kron(B, I) - torch.kron(I, B.T.contiguous())
    L = torch.cat([LA, LB], 0)
    s = torch.linalg.svdvals(L)
    return int((s < tol * max(1.0, float(s[0]))).sum())


def main():
    tag, a, ks, R, steps = sys.argv[1], float(sys.argv[2]), [int(x) for x in sys.argv[3].split(',')], int(sys.argv[4]), int(sys.argv[5])
    out = []
    for k in ks:
        mA, mB = spectra_balanced(k, a)
        t0 = time.time()
        best = (9.0, None)
        runs = []
        for s in range(R):
            D, U = optimise(mA, mB, seed=1000 * k + s, steps=steps)
            runs.append(D)
            print('n', sum(mA), 'seed', s, 'D %.5f' % D, flush=True)
            if D < best[0]:
                best = (D, U)
        A, B = pair_from_U(best[1], diag_from_mult(A_EIG, mA), diag_from_mult(B_EIG, mB))
        defs = exact_defects(A, B)
        n = A.shape[0]
        BA = B @ A
        P5 = torch.linalg.matrix_power(BA, 5)
        cd = commutant_dim(A, B) if n <= 36 else None
        rec = dict(n=n, a=a, multA=mA, multB=mB, runs=runs, best=best[0], defects=defs,
                   commutant_dim=cd, tr_BA=abs(complex(torch.trace(BA))) / n,
                   tr_BA5=abs(complex(torch.trace(P5))) / n, seconds=time.time() - t0)
        out.append(rec)
        print(json.dumps(rec), flush=True)
    json.dump(out, open(__file__.rsplit('/', 1)[0] + '/out_scaling_%s.json' % tag, 'w'), indent=1)


main()
