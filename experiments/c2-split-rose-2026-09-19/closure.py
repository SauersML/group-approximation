# Closure in (M_f)_H of the support of the canonical 2-cycle for the split-basis rose.
import itertools
from nlib import *
def cellpaths(letter, v):
    """2-cell sigma_letter at vertex v (a B-word): returns vertex reps along e (v -> v.letter) and
    along f_N(e) (v.phi -> ...), and the vertical ends."""
    fv = applyB(PHIB, v)
    along = [red2(fv + PHIB[letter][:i]) for i in range(len(PHIB[letter]) + 1)]
    return [v, red2(v + letter)], along
SUPPORT = [('a', 'ABCC', 1), ('b', '', 2), ('c', 'D', 2)]
if __name__ == '__main__':
    reps = []
    for l, v, _ in SUPPORT:
        e, fe = cellpaths(l, v)
        print(l, 'at', v, ' e:', e, ' f(e):', fe)
        reps += e + fe
    reps = sorted(set(reps), key=len)
    par = {r: r for r in reps}
    def fd(r):
        while par[r] != r: r = par[r]
        return r
    und = []
    for a, b in itertools.combinations(reps, 2):
        if fd(a) == fd(b): continue
        u = fromB(red2(a + inv2(b)))
        if inN(u): par[fd(b)] = fd(a)
        elif not notN(u): und.append((a, b))
    cls = {}
    for r in reps: cls.setdefault(fd(r), []).append(r)
    print(len(reps), 'reps,', len(cls), 'classes'); 
    for k, v in cls.items(): print('  ', v)
    print('undecided pairs:', len(und), und[:10])
