#!/usr/bin/env python3
"""Conjugacy of the subgroups of U used in sylow.py / pbar.py.

g in Sp_4(F_3) lifts to g~ in Sp_4(Z) with g~ = I mod 2 (Sp_4(Z) -> Sp_4(Z/6)
is onto), and g~ Gamma_V g~^-1 = Gamma_{g V g^-1}.  So subgroups V, V' of U
that are conjugate in Sp_4(F_3) give conjugate M_V, M_V' in Mod(S_2) and the
same census.  This script sorts the maximal subgroups max0..max3 and the
order-3 subgroups of Phi(U) into Sp_4(F_3)-classes, by brute force over all
51840 elements of Sp_4(F_3).
"""
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sylow as S  # noqa: E402


def keyset(V):
    return frozenset(S.key3(A) for A in V)


def sp_inv(g):
    return (-S.J3 @ g.T @ S.J3) % 3


def classes(subs, allg):
    ks = [keyset(V) for V in subs]
    label = [None] * len(subs)
    nxt = 0
    for i, V in enumerate(subs):
        if label[i] is not None:
            continue
        label[i] = nxt
        stack = np.array(V, dtype=np.int64)
        for g in allg:
            gi = sp_inv(g)
            conj = np.einsum("ij,ujk,kl->uil", g, stack, gi) % 3
            kc = frozenset(int(k) for k in S.key3(conj))
            for j in range(len(subs)):
                if label[j] is None and ks[j] == kc:
                    label[j] = nxt
        nxt += 1
    return label


def main():
    allg = S.sp4_f3()
    for g in allg[:50]:
        assert ((g.T @ S.J3 @ g) % 3 == S.J3).all()
    U = S.sylow_U(allg)
    Phi, r, maxes = S.frattini_maximals(U)
    out = {"max_classes": classes(maxes, allg)}
    Z = S.subgroup("z")
    out["Z_order"] = len(Z)
    ph = []
    k = 0
    while True:
        try:
            ph.append(S.subgroup(f"phisub{k}"))
        except IndexError:
            break
        k += 1
    out["phisub_count"] = len(ph)
    out["phisub_classes"] = classes(ph, allg)
    zk = keyset(Z)
    out["phisub_is_centre"] = [keyset(V) == zk for V in ph]
    out["phi_order"] = len(Phi)
    out["phi_is_abelian"] = all(
        S.key3((A @ B) % 3) == S.key3((B @ A) % 3) for A in Phi for B in Phi)
    print(json.dumps(out))
    json.dump(out, open(os.path.join(HERE, "orbits.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
