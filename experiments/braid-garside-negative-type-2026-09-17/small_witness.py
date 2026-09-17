"""Find a smallest subset of the radius-1 ball of B_3 (simple generators) on which the Charney
length fails to be conditionally negative definite, and print an exact integer witness."""
import itertools, numpy as np
from garside import Garside
from negtype import ball, kernel, top_eig, exact_witness
G = Garside(3)
F = ball(G, 1)
K = kernel(G, F)
for m in range(3, len(F) + 1):
    for S in itertools.combinations(range(len(F)), m):
        KS = K[np.ix_(S, S)]
        lam, v = top_eig(KS)
        if lam > 1e-6:
            for sc in (1, 2, 3, 5, 10, 100):
                c, val = exact_witness(KS, v, sc)
                if val > 0:
                    print("subset size", m, "lambda", lam)
                    for i, ci in zip(S, c):
                        print("  coeff", ci, "element (inf, factors)", F[i], "len", G.length(F[i]))
                    print("  c^T K c =", val, " sum c =", c.sum())
                    print("  K =\n", KS.astype(int))
                    raise SystemExit
