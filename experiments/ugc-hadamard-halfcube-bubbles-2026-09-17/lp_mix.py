"""Best mixture over t of the half-cube bubble adversaries H_t (minimax LP)."""
import sys
import numpy as np
from scipy.optimize import linprog
from halfcube_price import all_price_vectors


def best_mixture(vecs):
    V = np.array([[float(c) for c in v] for v in vecs])
    n, T = V.shape
    # variables q_0..q_{T-1}, z ; minimize z s.t. V q - z <= 0, sum q = 1
    c = np.zeros(T + 1)
    c[-1] = 1
    A = np.hstack([V, -np.ones((n, 1))])
    res = linprog(c, A_ub=A, b_ub=np.zeros(n), A_eq=[[1] * T + [0]], b_eq=[1],
                  bounds=[(0, None)] * T + [(None, None)], method="highs")
    return res.x[:T], res.x[-1]


if __name__ == "__main__":
    k = int(sys.argv[1])
    vecs = all_price_vectors(k)
    q, z = best_mixture(vecs)
    print("k", k, "vectors", len(vecs), "LP value", z)
    print("q", np.round(q, 5))
