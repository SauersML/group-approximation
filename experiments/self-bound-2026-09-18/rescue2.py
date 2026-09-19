"""For each two-swap rescue chain on onecyl(1,2,3,H,tw) (see chain123.py), check that both swaps leave b fixed and
change c only on top-row squares, so the chain is a pair of transpositions of the seam permutation sigma and its
effect on the excess is independent of H.  Prints, per (H, tw): number of chains, whether all are seam-only, and the
set of final seam permutations (as tuples, top-row square i -> bottom-row square)."""
import sys
from swap import Surf, apply_swap, excess, best_swap
from h2 import onecyl

def seam(c, H, n):
    return tuple(c[(H-1)*n + i] for i in range(n))

def run(H, tw):
    n = 6; b, c = onecyl(1, 2, 3, H, tw); S = Surf(b, c); A = S.cones()[0]; E0 = excess(b, c)
    secs = [(i // 4, i % 4) for i in S.cls[A]]; out = []; allseam = True
    for s1 in secs:
        for x in range(len(b)):
            s2 = (x, s1[1])
            if s2 == s1: continue
            r = apply_swap(S, [s1], [s2])
            if r is None or excess(*r) != E0: continue
            S2 = Surf(*r); r2 = best_swap(S2, 1, E0)
            if r2 is None or r2[2] != 0: continue
            b2, c2 = r2[3], r2[4]
            ok = (list(b2) == list(b) and list(r[0]) == list(b) and
                  all(c2[y] == c[y] and r[1][y] == c[y] for y in range((H-1)*n)))
            allseam &= ok; out.append((seam(r[1], H, n), seam(c2, H, n)))
    return len(out), allseam, sorted(set(out))

if __name__ == '__main__':
    for H in map(int, sys.argv[1:]):
        for tw in range(6):
            k, ok, fin = run(H, tw)
            print(H, tw, seam(onecyl(1, 2, 3, H, tw)[1], H, 6), k, ok, fin, flush=True)
