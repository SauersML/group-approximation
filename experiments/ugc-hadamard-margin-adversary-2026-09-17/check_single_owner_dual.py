"""Exact check of the dual certificate for single-owner radial adversaries.

Weights w_d = C / ((K-1-d)(K-2-d)), d = 0 .. K/4 - 1, C = (3K-4)(K-1)/K,
sum w_d = 1.  Labels in agree-view {C, -C, D, -D}; K cut(s, t, d) is the
level-averaged cut count of research/single-owner-radial-adversaries-stall-at-decoder-bound.
Shortest weighted path from start set {C, D} at d = 0 to end label at d = K/4:
  agree branch    (end D)  must be exactly 1,
  disagree branch (end -D) must be exactly 4 - 4/K.
Exact rational arithmetic (fractions).  Also cross-checks the table against
radial_zone_lp.cut_prob.
"""
import sys
from fractions import Fraction as Fr
import radial_zone_lp as R

LAB = ["C", "-C", "D", "-D"]


def kcut(s, t, d, K):
    """agree-view: D(x) = +1 iff i not in S(x); C = +1."""
    def v(lab, inS):
        base = 1 if lab.lstrip("-") == "C" else (-1 if inS else 1)
        return -base if lab.startswith("-") else base
    tot = 0
    for ix, iy, w in ((True, True, d), (False, True, 1), (False, False, K - d - 1)):
        if w and v(s, ix) != v(t, iy):
            tot += w
    return tot


def check(K):
    T = K // 4
    C = Fr((3 * K - 4) * (K - 1), K)
    w = [C / ((K - 1 - d) * (K - 2 - d)) for d in range(T)]
    assert sum(w) == 1
    for s in LAB:
        for t in LAB:
            for d in (0, T // 2, T - 1):
                assert Fr(kcut(s, t, d, K), K) == Fr(R.cut_prob(s, t, "agree", d, K)).limit_denominator(4 * K)
    out = {}
    for end in ("D", "-D"):
        V = {lab: (Fr(0) if lab == end else None) for lab in LAB}
        for d in range(T - 1, -1, -1):
            NV = {}
            for s in LAB:
                best = None
                for t in LAB:
                    if V[t] is None:
                        continue
                    c = w[d] * kcut(s, t, d, K) + V[t]
                    best = c if best is None or c < best else best
                NV[s] = best
            V = NV
        out[end] = min(V["C"], V["D"])
    assert out["D"] == 1, (K, out)
    assert out["-D"] == 4 - Fr(4, K), (K, out)
    return out


if __name__ == "__main__":
    for K in [int(a) for a in sys.argv[1:]] or [8, 16, 32, 64, 128, 256, 512, 1024]:
        o = check(K)
        print(K, "agree", o["D"], "disagree", o["-D"], "value at delta: 1 + delta *", o["-D"] - 1)
