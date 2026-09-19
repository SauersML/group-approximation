# Finite subcomplexes of (M_f)_H for the split-basis rose, with exact coset identification.
import itertools
from nlib import *
class Cosets:
    """Right cosets N u, u a B-word; equality by exact window membership, distinctness by finite covers."""
    def __init__(s): s.reps = []; s.cls = []
    def find(s, u):
        u = red2(u)
        for i, r in enumerate(s.reps):
            d = fromB(red2(u + inv2(r)))
            if inN(d): return i
            if not notN(d): raise ValueError('undecided coset pair %s %s' % (u, r))
        s.reps.append(u); return len(s.reps) - 1
class Cplx:
    """Vertices = coset ids. Edges: ('h', v, letter) from v to v.letter; ('t', v) from v to v.phi.
    Cells: (letter, v) = sigma over the edge ('h', v, letter)."""
    def __init__(s):
        s.C = Cosets(); s.E = set(); s.cells = []; s.base = s.C.find('')
    def walk(s, v, word):
        """Add the path reading `word` from vertex id v; return list of oriented edges and the end."""
        path = []
        for ch in word:
            u = s.C.reps[v]
            if ch.islower():
                t = s.C.find(u + ch); e = ('h', v, ch); path.append((e, 1))
            else:
                t = s.C.find(u + ch); e = ('h', t, ch.lower()); path.append((e, -1))
            s.E.add(e); v = t
        return path, v
    def tedge(s, v):
        e = ('t', v); s.E.add(e); return e, s.C.find(applyB(PHIB, s.C.reps[v]))
    def add_cell(s, letter, rep):
        v = s.C.find(rep)
        te, fv = s.tedge(v)
        pe, w = s.walk(v, letter)
        te2, fw = s.tedge(w)
        pf, end = s.walk(fv, PHIB[letter])
        assert end == fw
        bd = [(te, 1)] + pf + [(te2, -1)] + [(x, -o) for x, o in reversed(pe)]
        s.cells.append(((letter, v), bd)); return bd
    def ends(s, e):
        if e[0] == 't': return e[1], s.C.find(applyB(PHIB, s.C.reps[e[1]]))
        return e[1], s.C.find(s.C.reps[e[1]] + e[2])
    def label(s, e):
        """The word in x, y read along e (t reads y^-1: H a y^-1 = H phi(a))."""
        return 'Y' if e[0] == 't' else toxy(SPLIT[e[2]])
    def chi(s):
        V = {x for e in s.E for x in s.ends(e)}
        return len(V) - len(s.E) + len(s.cells), len(V), len(s.E), len(s.cells)
