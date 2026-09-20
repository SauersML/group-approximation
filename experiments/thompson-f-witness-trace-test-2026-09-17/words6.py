#!/usr/bin/env python3
"""List the cyclic classes (up to rotation and inversion) of reduced words of length <= L in F_2
lying in F' (exponent sums 0), with their normalized traces in each witness.  All are nontrivial in
F (no relation of F has length < 10).  In every trace of F they all equal tr(c) = tr([a,b])
(thompson-f-character-simplex: g in F' \\ {1} has trace 1 - t).

Usage: python3 words6.py L WITNESS.npy [...]"""

import sys
import numpy as np

from constrained_census import classes


def main():
    L = int(sys.argv[1])
    S = classes(L)
    for path in sys.argv[2:]:
        W = np.load(path)
        n = W.shape[-1]
        M = {"a": W[0], "A": W[0].conj().T, "b": W[1], "B": W[1].conj().T}
        trs = []
        for w in S:
            X = np.eye(n, dtype=complex)
            for x in w:
                X = X @ M[x]
            trs.append(np.real(np.trace(X)) / n)
        print(f"{path}: n={n} tr(c)={trs[0]:.4f}  max|tr(w)-tr(c)| over {len(S)} classes = "
              f"{max(abs(t - trs[0]) for t in trs):.4f}")
        print("   " + "  ".join(f"{w}:{t:+.3f}" for w, t in zip(S, trs)))


if __name__ == "__main__":
    main()
