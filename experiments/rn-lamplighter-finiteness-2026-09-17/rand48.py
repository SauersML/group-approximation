"""Random-path contraction test: for random g with lamps in [-W,W] and |shift|<=W, follow random paths of
length L in the 8-ary tree and record whether the section lands in the computed nucleus; also track the
largest section size seen at each depth."""
import random, sys, adt48
random.seed(1)
W, L, T = 60, 14, 300
for cl in ([], [0], [1], [-1]):
    c = frozenset(cl); N = adt48.nucleus(c)
    miss = 0; big = [0] * (L + 1)
    for _ in range(T):
        g = (frozenset(e for e in range(-W, W + 1) if random.random() < 0.5), random.randint(-W, W))
        for d in range(L + 1):
            big[d] = max(big[d], len(g[0]) + abs(g[1]))
            if d < L: g = random.choice(adt48.sections(g, c))
        if g not in N: miss += 1
    print("c=%s |N|=%d misses=%d/%d  max size by depth=%s" % (cl, len(N), miss, T, big))
