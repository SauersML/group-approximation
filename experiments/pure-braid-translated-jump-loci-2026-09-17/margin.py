"""Explicit radius of the open set of characters certified by a certificate file.

For every cell <C',F> with lowest vertex v and every other vertex D of star(F), the
certificate has the strict inequality  g(D) = f_{C'}(D) - f_{C'}(v) > 0, where
f_{C'}(D) = sum_{ij sep C',D} K a_ij + eta(D).  Changing a by delta (eta fixed) changes
g(D) by (sep(C',D) - sep(C',v)) . K delta, of absolute value at most
w(D) * K * |delta|_inf, where w(D) = number of pairs in exactly one of the two
separating sets.  So every a' with |a' - a|_inf < r = min_D g(D) / (w(D) K) realises
the same lowest-vertex assignment, hence the same ascending posets Asc(C), and is
certified by the same eta.  Prints r in the units of cert['a'].
Usage: python3 margin.py cert.json"""
import sys, json
from fractions import Fraction
import numpy as np
from fast_morse import Salvetti

def main():
    cert = json.load(open(sys.argv[1]))
    n, K = cert["n"], cert["K"]
    S = Salvetti(n)
    assert [tuple(c) for c in cert["chambers"]] == [tuple(c) for c in S.ch]
    a = np.array([int(x) * K for x in cert["a"]], dtype=np.int64)
    eta = np.array(cert["eta"], dtype=np.int64)
    best = None
    for k, (ci, F) in enumerate(S.cells):
        st = S.stars[F]
        sep = (S.side[st] != S.side[ci]).astype(np.int64)
        f = sep @ a + eta[st]
        j = int(np.argmin(f))
        assert (f == f[j]).sum() == 1
        for t in range(len(st)):
            if t == j:
                continue
            w = int(np.abs(sep[t] - sep[j]).sum())
            r = Fraction(int(f[t] - f[j]), w * K)
            if best is None or r < best:
                best = r
    print("certified radius (sup norm, units of a):", best, "=", float(best))

if __name__ == "__main__":
    main()
