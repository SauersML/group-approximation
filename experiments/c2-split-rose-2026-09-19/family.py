# Gluing-rank test (T5) on the family of roses in bases (a, b, c, d') = (pSr, rP, sR, w1 q w2), w1, w2 in <a,b,c>.
# Every such rose passes (T0): the canonical cycle is a@N S + 2 b@N + 2 c@N Q whatever d' is.
# Usage: python3 family.py [max length of w1, w2]
import sys, itertools
import nlib, cplx, minrank, dcell
from nlib import red, inv, inv2, red2, apply, PHI, PHII
def set_basis(w1, w2):
    """w1, w2 reduced words in a,b,c (new letters). Mutates the shared basis dictionaries in place."""
    old = lambda u: red(''.join(nlib.SPLIT[c] if c.islower() else inv(nlib.SPLIT[c.lower()]) for c in u))
    nlib.SPLIT['d'] = red(old(w1) + 'q' + old(w2))
    nlib.SPLITI['q'] = red2(inv2(w1) + 'd' + inv2(w2))
    for c in 'abcd': assert nlib.toB(nlib.SPLIT[c]) == c
    for c in 'pqrs': assert nlib.fromB(nlib.SPLITI[c]) == c
    for m, P in ((nlib.PHIB, PHI), (nlib.PHIBI, PHII)):
        for c in 'abcd': m[c] = nlib.toB(apply(P, nlib.SPLIT[c]))
    minrank.SUPPORT[:] = [(1, 'a', 'ABCC'), (2, 'b', ''), (2, 'c', inv2(nlib.SPLITI['q']))]
def test():
    """Return ('excluded', minrank) / ('open', details) / ('undecided', msg)."""
    try:
        K, occ, lens = minrank.setup()
        keys = sorted(occ, key=str)
        assert all(sum(x[2] for x in occ[e]) == 0 for e in keys), 'not a cycle'
        opts = [list(minrank.zero_partitions(occ[e])) for e in keys]
        best, keep = None, []
        for ch in itertools.product(*opts):
            blocks = [b for p in ch for b in p]; img = [keys[j] for j, p in enumerate(ch) for b in p]
            r = minrank.rank_of(blocks, lens)
            if best is None or r[0] < best: best = r[0]
            if r[0] <= 7: keep.append((blocks, img, r))
        if best > 7: return ('excluded-rank', best)
        E0 = set(K.E); hits = []
        dl = [v for v in range(len(K.C.reps)) if ('h', v, 'd') in E0]
        for blocks, img, r in keep:
            if r[3] > 1: return ('undecided', 'rank-7 gluing with %d components' % r[3])
            edges, fd = dcell.build(blocks, lens); verts = {x for e in edges for x in e}
            for v in dl:
                bd = dcell.dboundary(K, v)
                if bd is None or not all(e in E0 for e, _ in bd): continue
                for u in verts:
                    paths = [(u, [])]
                    for e, o in bd:
                        paths = [(b if o > 0 else a, p + [j]) for cur, p in paths
                                 for j, (a, b) in enumerate(edges) if img[j] == e and (a if o > 0 else b) == cur]
                    hits += [(v, u) for end, p in paths if end == u]
        return ('open', best, len(keep), hits) if hits else ('excluded-dcell', best, len(keep))
    except ValueError as ex: return ('undecided', str(ex))
if __name__ == '__main__':
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    words = ['']
    for n in range(L):
        words += [w + c for w in words if len(w) == n for c in 'abcABC' if not (w and w[-1] == c.swapcase())]
    tally = {}
    for w1, w2 in itertools.product(words, words):
        set_basis(w1, w2)
        res = test(); tally[res[0]] = tally.get(res[0], 0) + 1
        print(repr(w1), repr(w2), nlib.SPLIT['d'], res, flush=True)
    print('TALLY', tally)
