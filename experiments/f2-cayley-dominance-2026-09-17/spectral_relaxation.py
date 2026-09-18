#!/usr/bin/env python3
"""Spectral relaxations of the subgroup-dominance constant C(S) on F_2^k.

For S of measure mu = 2^-c put nu(chi) = hat f(chi)^2 / mu  (f = 1_S), a probability law on characters with
nu(0) = mu, and d_S(a) = 2 nu({chi : chi.a = 1}).  Every such nu satisfies, for every subspace B of F_2^k
(primal) with any basis b_1..b_r and every subspace W of the dual:

  (M)  nu(W) <= min(1, 2^(dim W - c))                                   [coset densities <= 1]
  (H)  2 sum_i nu({chi : chi.b_i = 1}) >= log2 1/nu(B^perp)             [Harper on cosets of B + Jensen]

The relaxed constant of a law nu is  C(nu) = min_p max_a Pr_p[a not in H] / d_nu(a),  d_nu(a) = 2 nu(chi.a = 1),
the min over distributions p on subgroups H of index 2^c.  It equals C(S) when nu = nu_S.

Modes:
  example c                  C(nu) for the mass-feasible law nu(0) = nu(e_i) = 2^-c on k = 2^c - 1  (exact LP)
  check k c trials seed      verify (M), (H) on random Boolean S (sanity)
  search k c mode R seed     alternate  w -> argmin_nu Phi_w(nu)  and  nu -> C(nu), dual w;
                             mode = mass | harper ; R restarts.  Prints best C(nu) found and its law.
"""
import itertools, math, sys, json
import numpy as np
from scipy.optimize import linprog

def popcount(x):
    return bin(x).count("1")

def subspaces(k, j):
    out = set()
    for piv in itertools.combinations(range(k), j):
        free = [(r, col) for r in range(j) for col in range(piv[r] + 1, k) if col not in piv]
        for bits in range(1 << len(free)):
            rows = [1 << (k - 1 - piv[r]) for r in range(j)]
            for t, (r, col) in enumerate(free):
                if bits >> t & 1:
                    rows[r] |= 1 << (k - 1 - col)
            span = {0}
            for rw in rows:
                span |= {x ^ rw for x in span}
            out.add(tuple(sorted(span)))
    return [list(t) for t in sorted(out)]

class Space:
    def __init__(self, k, c):
        self.k, self.c, self.N = k, c, 1 << k
        N = self.N
        self.P = np.array([[popcount(x & y) & 1 for y in range(N)] for x in range(N)], dtype=float)
        self.subs = {j: subspaces(k, j) for j in range(k + 1)}
        self.H = self.subs[k - c]                                    # subgroups of index 2^c
        self.miss = np.ones((len(self.H), N))
        for i, H in enumerate(self.H):
            self.miss[i, H] = 0
        self.miss = self.miss[:, 1:]                                  # a != 0
        # mass rows (M): dual subspaces of dim 1..c-1 (dim 0 is the equality nu(0) = 2^-c)
        self.mass_rows, self.mass_rhs = [], []
        for j in range(1, c):
            for W in self.subs[j]:
                r = np.zeros(N); r[W] = 1
                self.mass_rows.append(r); self.mass_rhs.append(2.0 ** (j - c))
        self.cuts, self.cut_rhs = [], []

    def perp(self, B):
        return [x for x in range(self.N) if all(popcount(x & b) & 1 == 0 for b in B)]

    def d_of(self, nu):
        return 2 * self.P[1:, :] @ nu                                  # d_nu(a), a = 1..N-1

    def C_of(self, nu):
        """min_p max_a Pr[a not in H]/d(a); returns value and dual generator law w."""
        d = self.d_of(nu)
        nH = len(self.H)
        cvec = np.zeros(nH + 1); cvec[-1] = 1
        A = np.hstack([self.miss.T, -d[:, None]])
        Aeq = np.concatenate([np.ones(nH), [0]])[None, :]
        res = linprog(cvec, A_ub=A, b_ub=np.zeros(len(d)), A_eq=Aeq, b_eq=[1],
                      bounds=[(0, None)] * (nH + 1), method="highs")
        assert res.status == 0, res.message
        w = -res.ineqlin.marginals
        w = np.maximum(w, 0); w = w / w.sum()
        return float(res.fun), w

    def harper_violations(self, nu, tol=1e-9):
        """for every primal subspace B (dim >= 1): min-weight basis sum vs log2 1/nu(B^perp)."""
        rho = np.concatenate([[0.0], self.d_of(nu)])
        out = []
        for r in range(1, self.k + 1):
            for B in self.subs[r]:
                vecs = sorted((x for x in B if x), key=lambda x: rho[x])
                basis, span = [], {0}
                for x in vecs:
                    if x not in span:
                        basis.append(x); span |= {y ^ x for y in span}
                        if len(basis) == r:
                            break
                Bp = self.perp(basis)
                m = float(nu[Bp].sum())
                lhs = float(sum(rho[b] for b in basis))
                rhs = -math.log2(max(m, 1e-300))
                if lhs < rhs - tol:
                    out.append((basis, Bp, m, lhs, rhs))
        return out

    def add_cut(self, basis, Bp, m):
        # L(nu) >= -log2 m0 - (x - m0)/(m0 ln 2),  x = nu(B^perp);  written as  -L - x/(m0 ln2) <= log2 m0 - 1/ln2
        N = self.N
        L = np.zeros(N)
        for b in basis:
            L += 2 * self.P[b, :]
        X = np.zeros(N); X[Bp] = 1
        m0 = max(m, 2.0 ** -self.c)
        self.cuts.append(-L - X / (m0 * math.log(2)))
        self.cut_rhs.append(math.log2(m0) - 1 / math.log(2))

    def best_nu(self, w, harper, rounds=60):
        """argmin over feasible nu of Phi_w(nu) = sum_a w_a d_nu(a)."""
        N, c = self.N, self.c
        obj = 2 * (w @ self.P[1:, :])
        Aeq = np.vstack([np.ones(N), np.eye(N)[0]])
        beq = [1.0, 2.0 ** -c]
        for _ in range(rounds):
            rows = self.mass_rows + self.cuts
            rhs = self.mass_rhs + self.cut_rhs
            res = linprog(obj, A_ub=np.array(rows) if rows else None, b_ub=np.array(rhs) if rows else None,
                          A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * N, method="highs")
            assert res.status == 0, res.message
            nu = res.x
            if not harper:
                return nu
            viol = self.harper_violations(nu)
            if not viol:
                return nu
            viol.sort(key=lambda v: v[3] - v[4])
            for basis, Bp, m, _, _ in viol[:40]:
                self.add_cut(basis, Bp, m)
        return nu                                                     # may be slightly infeasible: re-checked by caller

def nu_of_set(sp, S):
    N = sp.N
    f = np.zeros(N); f[list(S)] = 1
    fh = (1 - 2 * sp.P) @ f / N
    return fh ** 2 / (len(S) / N)

def main():
    mode = sys.argv[1]
    if mode == "example":
        c = int(sys.argv[2]); k = (1 << c) - 1
        sp = Space(k, c)
        nu = np.zeros(sp.N); nu[0] = 2.0 ** -c
        for i in range(k):
            nu[1 << i] = 2.0 ** -c
        mass_ok = all(r @ nu <= b + 1e-12 for r, b in zip(sp.mass_rows, sp.mass_rhs))
        C, w = sp.C_of(nu)
        viol = sp.harper_violations(nu)
        print(json.dumps({"c": c, "k": k, "C_nu": C, "formula": c * 2 ** (c - 1) / (2 ** c - 1),
                          "mass_ok": mass_ok, "harper_violations": len(viol),
                          "worst_harper": min((v[3] - v[4] for v in viol), default=0)}))
    elif mode == "check":
        k, c, trials, seed = map(int, sys.argv[2:6])
        sp = Space(k, c); rng = np.random.default_rng(seed)
        s = sp.N >> c; bad = 0
        for _ in range(trials):
            S = rng.choice(sp.N, s, replace=False)
            nu = nu_of_set(sp, S)
            mass_ok = all(r @ nu <= b + 1e-9 for r, b in zip(sp.mass_rows, sp.mass_rhs))
            if not mass_ok or sp.harper_violations(nu, 1e-9):
                bad += 1
        print(json.dumps({"k": k, "c": c, "trials": trials, "violating_sets": bad}))
    elif mode == "seeded":
        # local search over Boolean S (0 in S) maximising the true C(S) = C(nu_S), then climb the
        # (M)+(H) relaxation from the dual law w of the best set.
        k, c, iters, seed = map(int, sys.argv[2:6])
        sp = Space(k, c); rng = np.random.default_rng(seed); s = sp.N >> c
        S = [0] + list(rng.choice(np.arange(1, sp.N), s - 1, replace=False))
        bestS, (bestC, bw) = list(S), sp.C_of(nu_of_set(sp, S))
        for _ in range(iters):
            T = list(bestS)
            i = int(rng.integers(1, s)); out = [x for x in range(1, sp.N) if x not in T]
            T[i] = int(rng.choice(out))
            C, w = sp.C_of(nu_of_set(sp, T))
            if C >= bestC - 1e-12:
                bestS, bestC, bw = T, C, w
        relC, w = bestC, bw
        for it in range(12):
            nu = sp.best_nu(w, True)
            if sp.harper_violations(nu, 1e-6):
                break
            C, w = sp.C_of(nu)
            relC = max(relC, C)
        print(json.dumps({"k": k, "c": c, "true_C_best_set": bestC, "set": sorted(int(x) for x in bestS),
                          "relaxation_C_from_it": relC}))
    elif mode == "climb":
        # climb from an explicit Boolean seed set:  climb k c mass|harper x1,x2,...  [iters]
        k, c = int(sys.argv[2]), int(sys.argv[3]); harper = sys.argv[4] == "harper"
        S = [int(x) for x in sys.argv[5].split(",")]
        iters = int(sys.argv[6]) if len(sys.argv) > 6 else 15
        sp = Space(k, c)
        C0, w = sp.C_of(nu_of_set(sp, S)); best = (C0, None)
        for it in range(iters):
            nu = sp.best_nu(w, harper, rounds=200)
            if harper and sp.harper_violations(nu, 1e-6):
                print(json.dumps({"iter": it, "stopped": "cutting planes did not converge"})); break
            C, w = sp.C_of(nu)
            if C > best[0] + 1e-9:
                best = (C, nu.copy())
            print(json.dumps({"iter": it, "C_nu": round(C, 6)}), flush=True)
        out = {"k": k, "c": c, "mode": sys.argv[4], "seed_true_C": C0, "best_C_nu": best[0]}
        if best[1] is not None:
            out["support"] = {int(x): round(float(best[1][x]), 5) for x in range(sp.N) if best[1][x] > 1e-7}
        print(json.dumps(out))
    elif mode == "search":
        k, c = int(sys.argv[2]), int(sys.argv[3]); harper = sys.argv[4] == "harper"
        R, seed = int(sys.argv[5]), int(sys.argv[6])
        sp = Space(k, c); rng = np.random.default_rng(seed)
        best = (0, None)
        for r in range(R):
            w = rng.dirichlet(np.full(sp.N - 1, 0.3))
            for it in range(8):
                nu = sp.best_nu(w, harper)
                if harper and sp.harper_violations(nu, 1e-6):
                    break
                C, w = sp.C_of(nu)
                if C > best[0] + 1e-9:
                    best = (C, nu.copy())
            print(json.dumps({"restart": r, "best_C": round(best[0], 6)}), flush=True)
        nu = best[1]
        supp = {int(x): round(float(nu[x]), 5) for x in range(sp.N) if nu[x] > 1e-7}
        print(json.dumps({"k": k, "c": c, "mode": sys.argv[4], "best_C_nu": best[0], "support": supp}))

if __name__ == "__main__":
    main()
