#!/usr/bin/env python3
"""Write the stage-1 action and the verified Artin relation words as the text
input of rs_elim.cpp.  Twist words are t_S = (A_pq A_pr A_qr)^2 for the ten
3-subsets S in level8_purebraid.TRIPLES order.

A selection block follows: nsel, then nsel pairs (coset, twist index).  For
each label (S, mod-3 plane of (e1,f1), mod-3 plane of (e2,f2)), in both the
column and the row convention, the first PER pairs carrying that label are
selected (union over the two conventions).  Every separating-twist class
occurs among the selected vectors as long as the label is constant on classes
in at least one convention, which level6_lattice.py checks.

Usage: python3 level6_dump.py cosets.pkl out.txt [PER]
"""
import os
import pickle
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-level-eight-transversal-2026-09-17"))
import level8_purebraid as P  # noqa: E402
import numpy as np  # noqa: E402

sys.path.insert(0, HERE)
from level6_cosets import span3  # noqa: E402


def selection(objs, per=2):
    winv = {S: P.sigma_matrix(P.binv(P.CONJ[S])) for S in P.TRIPLES}
    seen = {"columns": {}, "rows": {}}
    sel = set()
    for c, key in enumerate(objs):
        A = np.array(key, dtype=np.int64).reshape(4, 4)
        for t, S in enumerate(P.TRIPLES):
            M = (A @ winv[S]) % 3
            X = M.T
            labs = {"columns": (S, span3([X[0], X[1]]), span3([X[2], X[3]])),
                    "rows": (S, span3([M[0], M[1]]), span3([M[2], M[3]]))}
            for conv, lab in labs.items():
                n = seen[conv].get(lab, 0)
                if n < per:
                    seen[conv][lab] = n + 1
                    sel.add((c, t))
    print("distinct labels", {k: len(v) for k, v in seen.items()},
          "selected", len(sel))
    return sorted(sel)


def word(w):
    return f"{len(w)} " + " ".join(f"{g} {e}" for g, e in w)


def main(inp, out, per=2):
    d = pickle.load(open(inp, "rb"))
    act, rels = d["act"], d["rels"]
    with open(out, "w") as fh:
        fh.write(f"{len(act)}\n")
        for row in act:
            fh.write(" ".join(map(str, row)) + "\n")
        fh.write(f"{len(rels)}\n")
        for lhs, rhs in rels:
            fh.write(word(lhs) + "\n" + word(rhs) + "\n")
        fh.write(f"{len(P.TRIPLES)}\n")
        for S in P.TRIPLES:
            fh.write(word(P.twist3(S) * 2) + "\n")
        sel = selection(d["objs"], int(per))
        fh.write(f"{len(sel)}\n")
        for c, t in sel:
            fh.write(f"{c} {t}\n")
    return sel


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
