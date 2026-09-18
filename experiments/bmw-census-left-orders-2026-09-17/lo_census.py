# Positive-cone ball-SAT on the parity kernel Gamma^+ and a finiteness (reducibility) test,
# for every one-vertex complete VH complex of a census produced by vh_enum.py.
import sys, json, time
from pysat.solvers import Cadical153, Glucose4

class VH:
    def __init__(s, iA, iB, SQ):
        s.iA, s.iB, s.m, s.n = iA, iB, len(iA), len(iB)
        s.SQ = SQ                      # (h,v) -> (v',h') with h v = v' h'
        s.H = [('h', x) for x in range(s.m)]; s.V = [('v', x) for x in range(s.n)]
    # complete rewriting system: c c^-1 -> 1, h v -> v' h'  (Newman: terminating + critical pairs)
    def rw(s, w):
        w = list(w); ch = True
        while ch:
            ch = False
            for i in range(len(w) - 1):
                p, q = w[i], w[i+1]
                if p[0] == q[0] and (s.iA if p[0] == 'h' else s.iB)[p[1]] == q[1]:
                    del w[i:i+2]; ch = True; break
                if p[0] == 'h' and q[0] == 'v':
                    v2, h2 = s.SQ[(p[1], q[1])]; w[i], w[i+1] = ('v', v2), ('h', h2); ch = True; break
        return tuple(w)
    def confluence(s):
        iA, iB, SQ = s.iA, s.iB, s.SQ; n = 0
        for h in range(s.m):
            for v in range(s.n):
                v3, h3 = SQ[(iA[h], v)]
                assert s.rw([('h', h), ('v', v3), ('h', h3)]) == (('v', v),)   # overlap h h^-1 v
                v2, h2 = SQ[(h, v)]
                assert s.rw([('v', v2), ('h', h2), ('v', iB[v])]) == (('h', h),)  # overlap h v v^-1
                n += 2
        return n
    @staticmethod
    def red(w, inv):
        out = []
        for c in w:
            if out and out[-1] == inv[c]: out.pop()
            else: out.append(c)
        return out
    def mul(s, g1, g2):
        SQ = s.SQ
        vs = list(g1[0]); h = list(g1[1])
        for v in g2[0]:
            for i in range(len(h) - 1, -1, -1):
                v, h[i] = SQ[(h[i], v)]
            if vs and vs[-1] == s.iB[v]: vs.pop()
            else: vs.append(v)
        for c in g2[1]:
            if h and h[-1] == s.iA[c]: h.pop()
            else: h.append(c)
        return (tuple(vs), tuple(h))

def ball(G, R):
    gens = [((v,), ()) for v in range(G.n)] + [((), (h,)) for h in range(G.m)]
    e = ((), ()); idx = {e: 0}; els = [e]; layer = [e]
    for d in range(R):
        nl = []
        for g in layer:
            for t in gens:
                x = G.mul(g, t)
                if x not in idx: idx[x] = len(els); els.append(x); nl.append(x)
        layer = nl
    return idx, els

def lo_sat(G, R, short=None):
    """CNF of the Lemma: variables p_g for g in K cap B_R, g != 1.
    short=None: clauses for all pairs g,h in K cap B_R with gh in B_R.
    short=k: only pairs where one factor has length <= k."""
    idx, els = ball(G, R)
    K = [i for i, (v, h) in enumerate(els) if i > 0 and len(v) % 2 == 0 and len(h) % 2 == 0]
    inv = {}
    for i in K:
        g = els[i]
        gi = G.mul(((tuple(G.iB[x] for x in reversed(g[0]))), ()), ((), tuple(G.iA[x] for x in reversed(g[1]))))
        # inverse of v h is h^-1 v^-1 = (normal form of) ; compute properly:
        gi = G.mul(((), tuple(G.iA[x] for x in reversed(g[1]))), (tuple(G.iB[x] for x in reversed(g[0])), ()))
        assert G.mul(g, gi) == ((), ())
        j = idx[gi]; assert j != i      # K is torsion-free
        inv[i] = j
    cls = []
    for i in K:
        if i < inv[i]: cls += [[i, inv[i]], [-i, -inv[i]]]
    if short is None:
        left = K
    else:
        left = [i for i in K if len(els[i][0]) + len(els[i][1]) <= short]
    seen = set()
    for i in left:
        gi = els[i]
        for j in K:
            for a, b in ((i, j), (j, i)):
                if (a, b) in seen: continue
                seen.add((a, b))
                k = idx.get(G.mul(els[a], els[b]))
                if k is None: continue
                cls.append([-a, -b] if k == 0 else [-a, -b, k])
    return len(els), len(K), cls

def solve(cls, both=True):
    res = []
    for S in ((Cadical153, Glucose4) if both else (Cadical153,)):
        with S(bootstrap_with=cls) as sv: res.append(sv.solve())
    assert len(set(res)) == 1
    return res[0]

def finite_image(G, horizontal=True, cap=4000):
    """Is the image of <A> (horizontal) in Aut(T_B) finite?  Automaton: state h, input v, SQ(h,v)=(v',h').
    Word w = h1..hk acts on v right-to-left.  E_n = elements given by length-n words; E_n subset E_{n+2}.
    Maintain a minimal automaton of all elements found; stop when E_{n+2} == E_n (then the group is
    E_n cup E_{n+1}, finite) or when more than cap elements (returns None: not certified finite)."""
    if horizontal:
        L, inp = G.m, G.n
        step = lambda a, v: G.SQ[(a, v)]            # -> (output v', section a')
    else:
        # vertical letters act on horizontal letters: from h v = v' h', v' acts... use v h^{-1}: 
        # h v = v' h'  <=>  v'^-1 h = h' v^-1 : letter v'^-1 on input h gives output h', section v^-1
        SQinv = {}
        for (h, v), (v2, h2) in G.SQ.items(): SQinv[(G.iB[v2], h)] = (h2, G.iB[v])
        L, inp = G.n, G.m
        step = lambda a, x: SQinv[(a, x)]
    # states of the letter automaton
    # element automaton: list of (out tuple, succ tuple of state ids)
    def minimize(outs, succ):
        # Moore partition refinement
        n = len(outs)
        cls = {}; part = [cls.setdefault(o, len(cls)) for o in outs]
        while True:
            sig = {}; new = [sig.setdefault((part[i], tuple(part[x] for x in succ[i])), len(sig)) for i in range(n)]
            if len(sig) == len(set(part)): return new
            part = new
    # identity element: out = identity, succ = itself
    states_out = [tuple(range(inp))]; states_succ = [(0,) * inp]
    level = [0]                      # E_0 as state ids
    levels = [set([0])]
    n = 0
    while True:
        # new product states (s, a): input x: step(a,x) = (x1, a'), then s on x1 -> out, s'
        base = len(states_out)
        pairs = [(s, a) for s in level for a in range(L)]
        pid = {p: base + k for k, p in enumerate(pairs)}
        # closure: sections of pair states are pairs (s', a') with s' in section-set of level; ensure present
        todo = list(pairs); k = 0
        outs = list(states_out); succ = list(states_succ)
        allp = dict(pid)
        extra_out = []; extra_succ = []
        while k < len(todo):
            s, a = todo[k]; k += 1
            o = []; sc = []
            for x in range(inp):
                x1, a2 = step(a, x)
                o.append(states_out[s][x1]); s2 = states_succ[s][x1]
                if (s2, a2) not in allp:
                    allp[(s2, a2)] = base + len(todo); todo.append((s2, a2))
                sc.append(allp[(s2, a2)])
            extra_out.append(tuple(o)); extra_succ.append(tuple(sc))
        outs += extra_out; succ += extra_succ
        part = minimize(outs, succ)
        # rebuild minimal automaton over classes
        ncls = max(part) + 1
        new_out = [None] * ncls; new_succ = [None] * ncls
        for i in range(len(outs)):
            c = part[i]
            if new_out[c] is None:
                new_out[c] = outs[i]; new_succ[c] = tuple(part[x] for x in succ[i])
        levels = [set(part[x] for x in lv) for lv in levels]
        newlevel = sorted(set(part[pid[p]] for p in pairs))
        levels.append(set(newlevel))
        states_out, states_succ = new_out, new_succ
        level = newlevel; n += 1
        if n >= 2 and levels[n] == levels[n - 2]:
            return len(levels[n] | levels[n - 1])
        if ncls > cap: return None

def load(path):
    D = json.load(open(path))
    for i, rep in enumerate(D['reps']):
        SQ = {tuple(a): tuple(b) for a, b in rep}
        yield i, VH(D['iA'], D['iB'], SQ)

if __name__ == "__main__":
    # usage: lo_census.py census.json   (pipeline: finiteness test; R4 all pairs; if irreducible-candidate
    # and SAT: R6 with one factor of length <= 4; if still SAT: R6 all pairs; then R8 one factor <= 2)
    path = sys.argv[1]
    lo, hi = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 10**9)
    for i, G in load(path):
        if not lo <= i < hi: continue
        G.confluence()
        fh = finite_image(G, True); fv = finite_image(G, False)
        rec = dict(idx=i, finH=fh, finV=fv)
        plan = [(4, None)]
        if fh is None or fv is None:
            plan += [(6, 4), (6, None), (8, 2)]
        for R, sh in plan:
            nb, nk, cls = lo_sat(G, R, sh)
            sat = solve(cls)
            rec[f'R{R}s{sh}'] = [sat, nb, nk, len(cls)]
            if not sat: break
        print(json.dumps(rec), flush=True)
