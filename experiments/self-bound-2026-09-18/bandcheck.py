"""Exhaustive search of vertex-admissible same-word loop pairs at A inside the band of vertex levels -1, 0, 1 of
the one-cylinder surface onecyl(a,b,c,4,tw) (levels 3, 0, 1; the band does not wrap).  By the reduction in the
proof (at most one seam visit, at most one pair-excursion per half-cylinder, excursions of width 1 or 2), every
vertex-admissible loop pair of the bi-infinite seam surface has a corner-equivalent one in this band, with the
same excess change.  Prints the number of admissible pairs and of lowering ones, and the longest pair seen."""
import sys
from swap import Surf, apply_swap, excess
from h2 import onecyl
from seambfs import level

def band_pairs(a, b, c, tw):
    n = a + b + c; H = 4; bb, cc = onecyl(a, b, c, H, tw); S = Surf(bb, cc)
    A = S.cones()[0]; dom = S.cls[A]; E0 = excess(bb, cc)
    secs = [(i // 4, i % 4) for i in dom]; tot = low = 0; Lmax = 0; ex_low = []
    for k in range(4):
        sk = [s for s in secs if s[1] == k]
        for s1 in sk:
            for s2 in sk:
                if s1 == s2: continue
                stack = [([s1], [s2], set())]
                while stack:
                    P, Q, used = stack.pop()
                    vp, vq = S.vend(P[-1]), S.vend(Q[-1])
                    if vp == A or vq == A:
                        if vp == A and vq == A:
                            r = apply_swap(S, P, Q)
                            if r is not None:
                                tot += 1; Lmax = max(Lmax, len(P))
                                if excess(*r) < E0: low += 1; ex_low.append(len(P))
                        continue
                    if vp == vq or vp in used or vq in used: continue
                    u2 = used | {vp, vq}
                    for mv in (0, 1, 2):
                        p2, q2 = S.step(P[-1], mv), S.step(Q[-1], mv)
                        if level(S, p2, n, H) not in (3, 0, 1): continue
                        stack.append((P + [p2], Q + [q2], u2))
    return tot, low, Lmax, sorted(set(ex_low))

if __name__ == '__main__':
    for abc in [(1, 2, 3), (1, 1, 4), (2, 2, 2), (1, 2, 4), (1, 3, 2)]:
        for tw in range(sum(abc)):
            print(abc, tw, band_pairs(*abc, tw), flush=True)
