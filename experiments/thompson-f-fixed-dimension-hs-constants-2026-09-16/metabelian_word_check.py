#!/usr/bin/env python3
"""Consistency check for Remark 4.2 of the artifact (the four-dimensional witness is not metabelian).

1. The relator words of thompson-f-metabelian-pairs-obey-sharp-linear-commutator-bound
   (bAABaaBAba, bAAABaaaBAAbaa) are cyclic conjugates of R1 = [ab^-1, a^-1ba], R2 = [ab^-1, a^-2ba^2].
2. The free-group identity c = u2 (a^2 R1 a^-2)(a R1 a^-1)(a^2 R2 a^-2)^-1 holds by free reduction.
3. u2 lies in F_2'': its image under the Magnus embedding of F_2/F_2'' is the identity (sympy).
4. Numerically, u2(U, W) is far from I on the stored n = 4, 6 witnesses, and ~0 on the n = 2 witness.

Item 4 is floating point and only illustrates; the rigorous conclusion of Remark 4.2 uses items 1-3 and
the exact inequality verified by replay_verify.py. Single-threaded; run with `timeout 600` from this directory.
"""
import json
import sys

import numpy as np
import sympy as sp

sys.path.insert(0, ".")
import ratio_search as rs  # noqa: E402


def inv(w):
    return "".join(ch.swapcase() for ch in reversed(w))


def red(w):
    st = []
    for ch in w:
        if st and st[-1] == ch.swapcase():
            st.pop()
        else:
            st.append(ch)
    return "".join(st)


def comm(x, y):
    return red(x + y + inv(x) + inv(y))


R1, R2, C = comm("aB", "Aba"), comm("aB", "AAbaa"), comm("a", "b")
N1, N2 = "bAABaaBAba", "bAAABaaaBAAbaa"
U2 = "abABaabAAABaaaBAbAAbaaBBabAAbaaBAA"


def rotations(w):
    return [w[i:] + w[:i] for i in range(len(w))]


ok1 = N1 in rotations(R1) and N2 in rotations(R2)
ok2 = red(U2 + "aa" + N1 + "AA" + "a" + N1 + "A" + inv("aa" + N2 + "AA")) == C

t1, t2, s1, s2 = sp.symbols("t1 t2 s1 s2")
MAG = {"a": sp.Matrix([[t1, s1], [0, 1]]), "b": sp.Matrix([[t2, s2], [0, 1]])}
MAG["A"], MAG["B"] = MAG["a"].inv(), MAG["b"].inv()
P = sp.eye(2)
for ch in U2:
    P = P * MAG[ch]
ok3 = sp.simplify(P - sp.eye(2)) == sp.zeros(2, 2)
print(json.dumps({"relators_are_cyclic_conjugates": ok1, "free_identity_holds": ok2, "u2_in_second_derived": bool(ok3)}))


def ev(word, U, W):
    M = {"a": U, "b": W, "A": U.conj().T, "B": W.conj().T}
    out = np.eye(U.shape[0], dtype=complex)
    for ch in word:
        out = out @ M[ch]
    return out


for n in (2, 4, 6):
    d = json.load(open(f"ratio_search_n{n}.json"))
    for row in d["rows"]:
        p = np.array(row["params"], dtype=float) / row["cayley_params_rounded_den"]
        U = rs.cayley(rs.skew_from_params(p[: n * n], n))
        W = rs.cayley(rs.skew_from_params(p[n * n:], n))
        hs = {name: float(np.sqrt(rs.e_float(ev(w, U, W)))) for name, w in (("c", C), ("R1", R1), ("R2", R2), ("u2", U2))}
        print(json.dumps({"n": n, "tau": row["tau"], "hs_c": round(hs["c"], 6),
                          "two_hs_R1_plus_hs_R2": round(2 * hs["R1"] + hs["R2"], 6), "hs_u2": round(hs["u2"], 6)}))
print("METABELIAN_CHECKS_HOLD" if (ok1 and ok2 and ok3) else "SOME_CHECK_FAILED")
