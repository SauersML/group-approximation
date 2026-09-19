"""The two-step rescue on onecyl(1,2,3,H,tw): swap 1 exchanges a one-edge path from a sector of the 6pi point A
with a one-edge path of the same direction from an arbitrary corner (a relocation move, excess-neutral); swap 2 is a
one-edge same-vertex slit pair (two sectors of one cone point, common end) that lowers the excess to 0.
For each (H, tw) prints the number of such chains and the set of (cone angles after swap 1 / 2pi, whether P2 starts
at a vertex adjacent to A, max-rank cost of the chain)."""
import sys
from swap import Surf, apply_swap, excess, best_swap, rank_minus_I, comp, inv
from h2 import onecyl

def rescue(H, tw):
    b, c = onecyl(1, 2, 3, H, tw); S = Surf(b, c); A = S.cones()[0]; E0 = excess(b, c)
    secs = [(i // 4, i % 4) for i in S.cls[A]]; found = []
    for s1 in secs:
        for x in range(len(b)):
            s2 = (x, s1[1])
            if s2 == s1: continue
            if True:
                r = apply_swap(S, [s1], [s2])
                if r is None or excess(*r) != E0: continue
                S2 = Surf(*r); cones = sorted(len(S2.cls[v]) // 4 for v in S2.cones())
                r2 = best_swap(S2, 1, E0)
                if r2 is not None and r2[2] == 0:
                    tot_b = rank_minus_I(comp(inv(b), r2[3])); tot_c = rank_minus_I(comp(inv(c), r2[4]))
                    found.append((cones, S.vstart(s2) == A, max(tot_b, tot_c)))
    return found

if __name__ == '__main__':
    for H in range(2, int(sys.argv[1]) + 1):
        for tw in range(6):
            f = rescue(H, tw)
            print(H, tw, len(f), sorted(set((tuple(x[0]), x[1], x[2]) for x in f)), flush=True)
