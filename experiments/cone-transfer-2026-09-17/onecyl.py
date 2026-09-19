"""One-cylinder square-tiled surfaces (w14-124).  Squares (i, r), 0 <= i < C, 0 <= r < H, index r*C + i.
b(i, r) = (i+1 mod C, r); c(i, r) = (i, r+1) for r < H-1 and c(i, H-1) = (sigma(i), 0).
The height r mod H is a well-defined function on S, so every loop has vertical holonomy in H*Z, and a loop of
nonzero vertical holonomy has length >= H.  Hence any handle (two loops at A with det(u, w) != 0) has length >= H.
Prints: excess, cone angles, profile lower bound over s,t <= smax (<= C by the proof), and the shortest
excess-lowering slit pair (best_swap).  Usage: python3 onecyl.py C H1 H2 ... (sigma chosen by search)."""
import sys, itertools
from swap import Surf, excess, profile, best_swap
def onecyl(C, H, sigma):
    idx = lambda i, r: r * C + i
    b = [0] * (C * H); c = [0] * (C * H)
    for r in range(H):
        for i in range(C):
            b[idx(i, r)] = idx((i + 1) % C, r)
            c[idx(i, r)] = idx(i, r + 1) if r < H - 1 else idx(sigma[i], 0)
    return b, c
def find_sigma(C):
    for sg in itertools.permutations(range(C)):
        b, c = onecyl(C, 1, sg); S = Surf(b, c)
        if excess(b, c) == 2 and len(S.cones()) == 1: return sg
C = int(sys.argv[1]); sg = find_sigma(C); print('C', C, 'sigma', sg)
for H in map(int, sys.argv[2:]):
    b, c = onecyl(C, H, sg); S = Surf(b, c)
    pr = profile(b, c, min(2 * H + 2, 14))
    bs = best_swap(S, C + 1)
    print('H', H, 'excess', excess(b, c), 'cones', [len(S.cls[v]) // 4 for v in S.cones()],
          'profile_lb %.3f at %s' % pr, 'best slit pair', None if bs is None else (bs[0], bs[1], bs[2], bs[5]))
