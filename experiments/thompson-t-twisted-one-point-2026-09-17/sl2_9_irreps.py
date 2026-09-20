"""Faithful complex irreps of SL(2,9) = 2.A_6 evaluated on the exact twisted solutions of sl2_twisted.py.

For every pair (a, b) in SL(2,9) with a^4 = -I, b^3 = I, (ba)^5 = I (up to conjugating a), and every
irreducible subrepresentation of the regular representation in which -I acts by -1, print the degree and
the operator-norm defects of (VU)^5, r_1, r_2, together with U^4 + 1 and V^3 - 1 (all should be ~0 except
the r_i that do not hold in SL(2,9)).

Irreps are split off by a random Hermitian element of the commutant (group average of a random matrix),
whose eigenspaces inside an isotypic component of an irrep of degree d are d copies of that irrep.
"""
import json

import numpy as np

import sl2_twisted as S


def main(seed=0):
    F = S.Fq(3, 2)
    mm, inv, I, mI = S.make(F)
    G = S.sl2(F)
    idx = {g: i for i, g in enumerate(G)}
    N = len(G)
    # left-regular permutation: L(g) e_h = e_{gh}
    perm = lambda g: np.array([idx[mm(g, h)] for h in G])

    def L(g):
        P = np.zeros((N, N))
        P[perm(g), np.arange(N)] = 1.0
        return P

    def LQ(g, Q):
        """L(g) @ Q without forming L(g): (L(g) Q)[g h] = Q[h]."""
        out = np.empty_like(Q)
        out[perm(g)] = Q
        return out

    rng = np.random.default_rng(seed)
    M = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
    M = M + M.conj().T
    # average M over LEFT translations: Mc = (1/N) sum_g L(g) M L(g)^*, which commutes with every L(g),
    # so its eigenspaces are L-invariant. With L(g) e_h = e_{pr[h]}, (L M L^T)[pr[i], pr[j]] = M[i, j].
    Mc = np.zeros((N, N), complex)
    for g in G:
        pr = perm(g)
        Mc[np.ix_(pr, pr)] += M
    Mc /= N
    LmI = L(mI)
    Pf = (np.eye(N) - LmI) / 2  # projection onto -I -> -1 part
    # restrict commutant element to faithful part
    w, Q = np.linalg.eigh(Pf)
    Qf = Q[:, w > 0.5]
    Mf = Qf.conj().T @ Mc @ Qf
    ev, E = np.linalg.eigh(Mf)
    # cluster eigenvalues
    blocks, cur = [], [0]
    for i in range(1, len(ev)):
        if ev[i] - ev[i - 1] < 1e-8:
            cur.append(i)
        else:
            blocks.append(cur)
            cur = [i]
    blocks.append(cur)
    sols = json.load(open("out_sl2_twisted.json"))[0]["examples"]
    # all solutions, not just examples
    A8 = [g for g in G if S.power(mm, g, 4, I) == mI]
    B3 = [g for g in G if g != I and S.power(mm, g, 3, I) == I]
    # one a per conjugacy class suffices (conjugate pairs give unitarily equivalent (U, V))
    reps, seenA = [], set()
    for a in A8:
        if a in seenA:
            continue
        reps.append(a)
        for g in G:
            seenA.add(mm(mm(g, a), inv(g)))
    pairs = [(a, b) for a in reps for b in B3 if S.power(mm, mm(b, a), 5, I) == I]
    out = {"n_blocks": len(blocks), "degrees": sorted(len(b) for b in blocks), "rows": []}
    seen_chars = {}
    for bl in blocks:
        Qb = Qf @ E[:, bl]
        d = len(bl)
        # character on a few elements to identify the irrep
        chi = tuple(np.round([np.trace(Qb.conj().T @ LQ(g, Qb)) for g in G[:40]], 6))
        key = (d, chi)
        if key in seen_chars:
            continue
        seen_chars[key] = True
        best = {"r1": 9, "r2": 9, "max": 9}
        ok_rows = []
        for a, b in pairs:
            U = Qb.conj().T @ LQ(a, Qb)
            V = Qb.conj().T @ LQ(b, Qb)
            X = V @ U @ V
            J = U @ U
            W = J @ V @ V @ J
            P5 = np.linalg.matrix_power(V @ U, 5)
            Y1 = J @ X @ J.conj().T
            Y2 = W @ X @ W.conj().T
            nrm = lambda Mx: float(np.linalg.norm(Mx, 2))
            row = {
                "U4+1": nrm(np.linalg.matrix_power(U, 4) + np.eye(d)),
                "V3-1": nrm(np.linalg.matrix_power(V, 3) - np.eye(d)),
                "pent": nrm(P5 - np.eye(d)), "r1": nrm(X @ Y1 - Y1 @ X), "r2": nrm(X @ Y2 - Y2 @ X),
            }
            ok_rows.append(row)
        r1s = sorted(set(round(r["r1"], 6) for r in ok_rows))
        r2s = sorted(set(round(r["r2"], 6) for r in ok_rows))
        mx = min(max(r["pent"], r["r1"], r["r2"]) for r in ok_rows)
        exact_err = max(max(r["U4+1"], r["V3-1"], r["pent"]) for r in ok_rows)
        rec = {"degree": d, "n_pairs": len(ok_rows), "r1_values": r1s, "r2_values": r2s,
               "min_full_defect": mx, "max_exactness_error": exact_err,
               "U_eig_angles_over_pi": sorted(np.round(np.angle(np.linalg.eigvals(
                   Qb.conj().T @ LQ(pairs[0][0], Qb))) / np.pi, 6).tolist()),
               "V_eig_angles_over_pi_first_pair": sorted(np.round(np.angle(np.linalg.eigvals(
                   Qb.conj().T @ LQ(pairs[0][1], Qb))) / np.pi, 6).tolist()),
               "r1_r2_pairs": sorted(set((round(r["r1"], 6), round(r["r2"], 6)) for r in ok_rows))}
        print(json.dumps(rec), flush=True)
        out["rows"].append(rec)
    json.dump(out, open("out_sl2_9_irreps.json", "w"), indent=1)


if __name__ == "__main__":
    main()
