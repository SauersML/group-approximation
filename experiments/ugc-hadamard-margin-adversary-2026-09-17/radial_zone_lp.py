"""Radial zone adversaries for Had_k -> Max-2Lin(2) gadgets (k large).

Setting (hadamard-gadget-deletion-ratio-window): R*(k) = K min_A max_e
Pr[A cuts e] over folded A random on P = {chi_a}; K = 2^k.

Adversary family Z(delta = 1/2):
  xi uniform on {-1,1}^P, (i, tau) uniform and independent of xi.
  Zone of the signed primary y0 = s chi_p: {x : d(x, y0) < K/4}.  Zones of
  distinct signed primaries are at distance >= 2 (never adjacent).
  Branch of p: agree if xi_p = tau chi_p(i), else disagree (prob 1/2 each).
  In the zone, A(x) = L(d(x,y0)) applied to x, where L(d) is a random
  label in {C, -C, D, -D}:
      C(x) = s xi_p,  D(x) = tau x_i,  and their negations,
  and L is a Markov chain in d (its law may depend on the branch).
  Outside all zones, A(x) = tau x_i (label D at d = K/4).
  Folded and random on P provided L(0) in {C} U {labels equal to C at y0}.

For an edge x -> y = x^j with d(y,y0) = d(x,y0) + 1 = d + 1 the cut
probability depends only on (L(d), L(d+1), branch, d), because given the
branch, i is uniform and  D(x) = C(x)  iff  [i in S(x)] = [branch=disagree],
S(x) the flip set of x relative to y0.

The LP minimizes R over pair laws mu_d(s, s') (Markov consistency) with
   sum_branch Pr[branch] K Pr[cut | branch] <= R   for every d = 0 .. K/4 - 1,
with Pr[disagree] = delta (default 1/2, the independent case).
Every other edge costs exactly 1.  The LP value is an upper bound on R*(k)
for every k (it is a feasible adversary), exact rational check separately.
"""
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

LAB = ["C", "-C", "D", "-D"]


def cut_prob(s, t, branch, d, K):
    """Pr_i[ s(x) != t(y) ] with |S(x)| = d, S(y) = S(x) + {j}."""
    # value of each label relative to C, as a function of the event E = [i in S]
    # agree:    D = C  iff i not in S ;  disagree: D = C iff i in S
    def rel(lab, inS):
        if lab == "C":
            return 1
        if lab == "-C":
            return -1
        dv = (1 if not inS else -1) if branch == "agree" else (1 if inS else -1)
        return dv if lab == "D" else -dv
    # i uniform over K coords: i in S(x) (d), i = j (1), else (K-d-1)
    tot = 0.0
    for inSx, inSy, w in ((True, True, d), (False, True, 1), (False, False, K - d - 1)):
        if w == 0:
            continue
        if rel(s, inSx) != rel(t, inSy):
            tot += w
    return tot / K


def solve(K, verbose=False, delta=0.5):
    T = K // 4
    nl = len(LAB)
    # variables: mu[b][d][s][t] for d = 0..T-1, then R
    nb = 2
    idx = lambda b, d, s, t: ((b * T + d) * nl + s) * nl + t
    nv = nb * T * nl * nl + 1
    Ri = nv - 1
    c = np.zeros(nv); c[Ri] = 1.0
    Aub = lil_matrix((T, nv)); bub = np.zeros(T)
    Aeq_rows = []; beq = []
    branches = ["agree", "disagree"]
    for d in range(T):
        for b, br in enumerate(branches):
            for s in range(nl):
                for t in range(nl):
                    Aub[d, idx(b, d, s, t)] += (1 - delta if br == "agree" else delta) * K * cut_prob(LAB[s], LAB[t], br, d, K)
        Aub[d, Ri] = -1.0
    Aeq = lil_matrix((nb * (T + 1) * nl + nb, nv))
    r = 0
    for b, br in enumerate(branches):
        # total mass 1 at d = 0
        for s in range(nl):
            for t in range(nl):
                Aeq[r, idx(b, 0, s, t)] = 1.0
        beq.append(1.0); r += 1
        # L(0) must equal C at y0 (S empty): C always; D iff agree; -D iff disagree
        ok0 = {"C", "D"} if br == "agree" else {"C", "-D"}
        for s in range(nl):
            if LAB[s] not in ok0:
                for t in range(nl):
                    Aeq[r, idx(b, 0, s, t)] = 1.0
                beq.append(0.0); r += 1
        # consistency: sum_s mu_{d-1}(s, t) = sum_u mu_d(t, u)
        for d in range(1, T):
            for t in range(nl):
                for s in range(nl):
                    Aeq[r, idx(b, d - 1, s, t)] += 1.0
                for u in range(nl):
                    Aeq[r, idx(b, d, t, u)] -= 1.0
                beq.append(0.0); r += 1
        # L(T) = D
        for s in range(nl):
            for t in range(nl):
                if LAB[t] != "D":
                    Aeq[r, idx(b, T - 1, s, t)] = 1.0
        beq.append(0.0); r += 1
    Aeq = Aeq[:r]
    bounds = [(0, None)] * nv
    res = linprog(c, A_ub=Aub.tocsr(), b_ub=bub, A_eq=Aeq.tocsr(), b_eq=np.array(beq),
                  bounds=bounds, method="highs")
    return res


if __name__ == "__main__":
    for K in [int(a) for a in sys.argv[1:]] or [64, 128, 256, 512, 1024, 2048]:
        res = solve(K)
        print(K, res.status, res.fun)
