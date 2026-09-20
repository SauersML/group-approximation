"""Brute-force checks for coarsening-derivatives-are-block-rigid-and-window-avoiding.

Trees are tuples of leaves (binary strings) in lex order; Moore's partial right action,
generators given by their piece maps (arXiv:0905.1118v7, Sec. 2).

Checks, for all trees with at most NMAX leaves:
 (W) for every U dominated by T:
     [for all gamma: T.gamma defined <=> U.gamma defined]
     <=> [no leaf u of U in W={'',0,1,10,11} has |T/u|>=2]  or  [U=('',) and T=('0','1')];
 (R) if U.gamma is defined then the leaf-index blocks of T over U are carried to blocks of
     T.gamma over U.gamma with identical block shapes;
 (S) for every T and l with T.x0^j defined for j<l, every leaf-index interval partition pi
     that is a window-avoiding block partition of each T.x0^j (j<l) has >= l-1 blocks.
"""
import itertools, sys

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 8

GENS = {
    'x0':   [('00', '0'), ('01', '10'), ('1', '11')],
    'x1':   [('0', '0'), ('100', '10'), ('101', '110'), ('11', '111')],
}
GENS['x0i'] = [(b, a) for a, b in GENS['x0']]
GENS['x1i'] = [(b, a) for a, b in GENS['x1']]
W = {'', '0', '1', '10', '11'}


def trees(n):
    if n == 1:
        return [('',)]
    out = []
    for k in range(1, n):
        for L in trees(k):
            for R in trees(n - k):
                out.append(tuple('0' + s for s in L) + tuple('1' + s for s in R))
    return out


def act(T, g):
    res = []
    for leaf in T:
        for s, t in GENS[g]:
            if leaf.startswith(s):
                res.append(t + leaf[len(s):])
                break
        else:
            return None
    return tuple(res)


def coarsenings(T):
    """All U dominated by T (U is T with some subtrees collapsed)."""
    if len(T) == 1:
        return [('',)]
    L = tuple(s[1:] for s in T if s[0] == '0')
    R = tuple(s[1:] for s in T if s[0] == '1')
    out = [('',)]
    for a in coarsenings(L):
        for b in coarsenings(R):
            out.append(tuple('0' + s for s in a) + tuple('1' + s for s in b))
    return out


def blocks(T, U):
    """Leaf-index intervals of T under each leaf of U, and the block shapes."""
    iv, shapes, i = [], [], 0
    for u in U:
        sub = tuple(s[len(u):] for s in T if s.startswith(u))
        iv.append((i, i + len(sub)))
        shapes.append(sub)
        i += len(sub)
    return iv, shapes


def window_ok(T, U):
    return all(not (u in W and sum(1 for s in T if s.startswith(u)) >= 2) for u in U)


def check():
    nW = nR = nS = 0
    for n in range(1, NMAX + 1):
        for T in trees(n):
            for U in coarsenings(T):
                lhs = all((act(T, g) is not None) == (act(U, g) is not None) for g in GENS)
                rhs = window_ok(T, U) or (U == ('',) and T == ('0', '1'))
                assert lhs == rhs, (T, U)
                nW += 1
                iv, sh = blocks(T, U)
                for g in GENS:
                    Ug = act(U, g)
                    if Ug is None:
                        continue
                    Tg = act(T, g)
                    assert Tg is not None
                    iv2, sh2 = blocks(Tg, Ug)
                    assert iv2 == iv and sh2 == sh, (T, U, g)
                    nR += 1
    # (S): spine count, trees up to NMAX leaves
    for n in range(2, NMAX + 1):
        for T in trees(n):
            chain = [T]
            while True:
                nxt = act(chain[-1], 'x0')
                if nxt is None:
                    break
                chain.append(nxt)
            for l in range(1, len(chain) + 1):
                seg = chain[:l]
                best = None
                for U in coarsenings(T):
                    iv, _ = blocks(T, U)
                    ok = True
                    for Tj in seg:
                        # the same index partition must be a block partition of Tj
                        Uj = [c for c in coarsenings(Tj) if blocks(Tj, c)[0] == iv]
                        if not Uj or not window_ok(Tj, Uj[0]):
                            ok = False
                            break
                    if ok:
                        best = len(U) if best is None else min(best, len(U))
                if best is not None:
                    assert best >= l - 1, (T, l, best)
                    nS += 1
    print(f"NMAX={NMAX}: (W) {nW} pairs, (R) {nR} edges, (S) {nS} segments: all pass")


if __name__ == '__main__':
    check()
