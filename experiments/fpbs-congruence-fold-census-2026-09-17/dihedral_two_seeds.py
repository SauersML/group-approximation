"""Exact check: in the regular D_N-set with a = r (rotation), b = s (reflection),
which 2-element seed sets percolate under the 2-of-3 rule on T_g = (g, a g, b g)?
Element r^k s^e is coded (k, e). Left multiplication: r.(k,e) = (k+1, e),
s.(k,e) = (-k, 1-e). Prints, for each N, whether {e, s} = {(0,0),(0,1)} percolates,
and the number of percolating pairs.
"""
from itertools import combinations


def closure(N, seeds, mode=0):
    def ra(x): return ((x[0] + 1) % N, x[1])
    def sa(x): return ((-x[0]) % N, 1 - x[1])
    ga, gb = (ra, sa) if mode == 0 else (sa, ra)
    inf = set(seeds)
    changed = True
    while changed:
        changed = False
        for k in range(N):
            for e in (0, 1):
                g = (k, e); T = [g, ga(g), gb(g)]
                c = sum(1 for x in T if x in inf)
                if c >= 2:
                    for x in T:
                        if x not in inf:
                            inf.add(x); changed = True
    return len(inf)


if __name__ == '__main__':
    for mode in (0, 1):
        for N in list(range(2, 16)) + [31, 64, 101]:
            elts = [(k, e) for k in range(N) for e in (0, 1)]
            ok = closure(N, [(0, 0), (0, 1)], mode) == 2 * N
            ok2 = closure(N, [(0, 0), (1, 0)], mode) == 2 * N
            npairs = sum(1 for p in combinations(elts, 2) if closure(N, p, mode) == 2 * N) if N <= 13 else -1
            print(f"mode={mode} N={N}: {{e,s}} percolates={ok}  {{e,r}} percolates={ok2}  percolating pairs={npairs}")
