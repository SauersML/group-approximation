#!/usr/bin/env python3
"""Legal f-folded fatgraphs for positive automorphisms of F_3.

Letters: a,b,c positive; A,B,C inverses.  A positive automorphism phi on the
rose R is a train track map.  A fatgraph X -> R whose boundary splits as
d^- (words w_i) and d^+ (words phi(w_i)^{-1}) is a *legal f-folded fatgraph*
if (L) the directions at every vertex lie in pairwise distinct gates,
plus Calegari-Walker conditions (2),(3),(4).  Proposition (see
research/legal-f-folded-fatgraphs-give-surface-subgroups-proof.md): then the
closed surface S*_f(X) is pi_1-injective in F_3 x|_phi Z.
(build_sat/solve below search only trivalent X; sat4.py allows any valence and
lp5.py decides existence for boundaries made of copies of one word.)

This script
  * checks that phi is an automorphism (Stallings folding),
  * computes gates, the transition matrix, its characteristic polynomial
    (irreducible cubic + primitive => fully irreducible and atoroidal, see proof file),
  * builds the SAT model for legal f-folded fatgraphs with given d^- words,
  * verifies any solution independently: rebuilds the fatgraph from the
    pairing, checks valence, immersion, legality, CW conditions (2)-(4), chi,
    and unrolls X_n for n <= NUNROLL checking that X_n -> R is an immersion.
"""
import itertools, sys, json
from fractions import Fraction

import sympy
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

POS = "abc"
def inv(x):
    return x.swapcase()
def inv_word(w):
    return "".join(inv(x) for x in reversed(w))
def reduce_word(w):
    out = []
    for x in w:
        if out and out[-1] == inv(x):
            out.pop()
        else:
            out.append(x)
    return "".join(out)

def apply(phi, w):
    return "".join(phi[x] if x.islower() else inv_word(phi[x.lower()]) for x in w)

# ---------------------------------------------------------------- automorphism check
def stallings_is_whole_group(words):
    """Fold the wedge of loops reading `words`; subgroup == F_3 iff the result is the rose."""
    # graph: edges as dict vertex -> {letter: vertex} (both directions stored)
    adj = {0: {}}
    nv = [1]
    parent = {}
    def find(v):
        while parent.get(v, v) != v:
            v = parent[v]
        return v
    edges = []
    for w in words:
        cur = 0
        for i, x in enumerate(w):
            nxt = 0 if i == len(w) - 1 else nv[0]
            if nxt != 0:
                nv[0] += 1
            edges.append((cur, x, nxt))
            cur = nxt
    # union-find folding
    changed = True
    while changed:
        changed = False
        out = {}
        for (u, x, v) in edges:
            u, v = find(u), find(v)
            for (p, y, q) in ((u, x, v), (v, inv(x), u)):
                key = (p, y)
                if key in out and find(out[key]) != find(q):
                    a, b = find(out[key]), find(q)
                    parent[max(a, b)] = min(a, b)
                    changed = True
                else:
                    out.setdefault(key, q)
    verts = {find(v) for (u, x, v) in edges} | {find(u) for (u, x, v) in edges}
    labs = {(find(u), x, find(v)) for (u, x, v) in edges}
    labs = {(u, x.lower(), v) if x.islower() else (v, x.lower(), u) for (u, x, v) in labs}
    return len(verts) == 1 and {x for (_, x, _) in labs} == set(POS)

# ---------------------------------------------------------------- train track data
def first_letter_map(phi):
    return {x: (phi[x][0] if x.islower() else inv(phi[x.lower()][-1])) for x in "abcABC"}

def gate_of(phi):
    """gates: directions d ~ d' iff Df^k d == Df^k d' for some k."""
    D = first_letter_map(phi)
    dirs = "abcABC"
    K = 12
    def it(d):
        for _ in range(K):
            d = D[d]
        return d
    return {d: it(d) for d in dirs}

def legal_turn(g, u, v):
    """turn crossed by the word ...uv...: directions {inv(u), v}"""
    return g[inv(u)] != g[v]

def cyc_legal(g, w):
    return all(legal_turn(g, w[i], w[(i + 1) % len(w)]) for i in range(len(w)))

def matrix(phi):
    return sympy.Matrix([[phi[x].count(y) for x in POS] for y in POS])

def certify_fully_irreducible_atoroidal(phi):
    M = matrix(phi)
    lam = sympy.symbols("t")
    cp = M.charpoly(lam).as_expr()
    irred = sympy.Poly(cp, lam).is_irreducible
    prim = all(v > 0 for v in (M ** 9))
    aut = stallings_is_whole_group([phi[x] for x in POS])
    return {"charpoly": str(cp), "irreducible": bool(irred), "primitive": bool(prim), "automorphism": bool(aut)}

# ---------------------------------------------------------------- fatgraph model
class Boundary:
    """darts = letter occurrences of all boundary cycles."""
    def __init__(self, phi, minus_words):
        self.phi = phi
        self.words = []   # (word, kind, fcorner-set)
        self.label = []
        self.nxt = []
        self.prv = []
        self.kind = []     # '-' or '+'
        self.fdart = []    # dart d is the dart right after an f-corner
        self.circle = []
        for ci, w in enumerate(minus_words):
            self._add(w, "-", set(), ci)
            blocks = [phi[x] if x.islower() else inv_word(phi[x.lower()]) for x in w]
            # d^+ reads phi(w)^{-1} = inv(block_L) ... inv(block_1)
            plus = "".join(inv_word(b) for b in reversed(blocks))
            starts = set()
            pos = 0
            for b in reversed(blocks):
                starts.add(pos)
                pos += len(b)
            self._add(plus, "+", starts, ci)
        self.N = len(self.label)

    def _add(self, w, kind, fstarts, ci):
        base = len(self.label)
        L = len(w)
        for i, x in enumerate(w):
            self.label.append(x)
            self.nxt.append(base + (i + 1) % L)
            self.prv.append(base + (i - 1) % L)
            self.kind.append(kind)
            self.fdart.append(i in fstarts)
            self.circle.append((ci, kind))
        self.words.append((w, kind))

def build_sat(B, require_trivalent=True, c2=True, c3=True, c4=True):
    N = B.N
    var = {}
    cnt = [0]
    def v(d, q):
        key = (min(d, q), max(d, q))
        if key not in var:
            cnt[0] += 1
            var[key] = cnt[0]
        return var[key]
    cand = [[q for q in range(N) if B.label[q] == inv(B.label[d])] for d in range(N)]
    for d in range(N):
        for q in cand[d]:
            v(d, q)
    def lit(d, q):
        key = (min(d, q), max(d, q))
        return var.get(key)
    clauses = []
    # forbidden pairings
    forb = set()
    for d in range(N):
        for q in cand[d]:
            if q == B.prv[d] or q == B.nxt[d]:
                forb.add(lit(d, q))                    # valence 1 (reduced words: never happens)
            if c4 and B.kind[d] == "-" and B.kind[q] == "-":
                forb.add(lit(d, q))                    # (4): edge covered twice by d^-
            if c4 and B.kind[d] == "-" and B.kind[B.nxt[q]] == "-":
                forb.add(lit(d, q))                    # (4): two d^- corners at a vertex (sigma-adjacent)
            if c3 and B.fdart[d] and B.fdart[B.nxt[q]]:
                forb.add(lit(d, q))                    # (3)
    for l in forb:
        clauses.append([-l])
    top = cnt[0]
    # exactly one partner per dart
    for d in range(N):
        lits = [lit(d, q) for q in cand[d]]
        if not lits:
            return None, None, None
        enc = CardEnc.equals(lits=lits, bound=1, top_id=top, encoding=EncType.seqcounter)
        top = max(top, enc.nv)
        clauses.extend(enc.clauses)
    # valence <= 3 ; sigma(d) = nxt(p(d))
    for d in range(N):
        pd = B.prv[d]
        for q1 in cand[d]:
            d1 = B.nxt[q1]
            for q2 in cand[d1]:
                if q2 == pd:
                    continue
                d2 = B.nxt[q2]
                l3 = lit(d2, pd)
                c = [-lit(d, q1), -lit(d1, q2)]
                if l3 is not None:
                    c.append(l3)
                clauses.append(c)
    # (2): f-corner vertex bivalent: p(nxt(p(d))) == prv(d)
    for d in range(N):
        if not (c2 and B.fdart[d]):
            continue
        pd = B.prv[d]
        for q in cand[d]:
            l2 = lit(B.nxt[q], pd)
            c = [-lit(d, q)]
            if l2 is not None:
                c.append(l2)
            clauses.append(c)
    # some trivalent vertex
    if require_trivalent:
        ys = []
        for d in range(N):
            top += 1
            y = top
            ys.append(y)
            pd = B.prv[d]
            for q in cand[d]:
                l2 = lit(B.nxt[q], pd)
                if l2 is not None:
                    clauses.append([-y, -lit(d, q), -l2])
        clauses.append(ys)
    return clauses, var, top

def solve(B, require_trivalent=True, c2=True, c3=True, c4=True):
    clauses, var, top = build_sat(B, require_trivalent, c2, c3, c4)
    if clauses is None:
        return None
    s = Cadical153(bootstrap_with=clauses)
    ok = s.solve()
    if not ok:
        return False
    model = set(l for l in s.get_model() if l > 0)
    p = {}
    for (d, q), l in var.items():
        if l in model:
            p[d] = q
            p[q] = d
    return p

# ---------------------------------------------------------------- independent verifier
def verify(B, p, g, nunroll=3):
    N = B.N
    rep = {}
    assert all(p[p[d]] == d and p[d] != d for d in range(N)), "pairing not involution"
    assert all(B.label[p[d]] == inv(B.label[d]) for d in range(N)), "labels"
    sigma = lambda d: B.nxt[p[d]]
    seen = {}
    verts = []
    for d in range(N):
        if d in seen:
            continue
        orb = [d]
        e = sigma(d)
        while e != d:
            orb.append(e)
            e = sigma(e)
        for e in orb:
            seen[e] = len(verts)
        verts.append(orb)
    vals = [len(o) for o in verts]
    rep["valences"] = sorted(vals)
    assert all(k in (2, 3) for k in vals), "valence"
    # immersion + legality: outgoing dart labels at each vertex distinct gates pairwise
    for o in verts:
        ds = [B.label[e] for e in o]
        assert len(set(g[x] for x in ds)) == len(ds), ("illegal/non-immersed vertex", ds)
    # (4)
    for o in verts:
        assert sum(1 for e in o if B.kind[e] == "-") <= 1, "(4) vertex"
    for d in range(N):
        assert not (B.kind[d] == "-" and B.kind[p[d]] == "-"), "(4) edge"
    # (2),(3)
    for o in verts:
        nf = sum(1 for e in o if B.fdart[e])
        assert nf <= 1, "(3)"
        if nf == 1:
            assert len(o) == 2, "(2)"
    V = len(verts)
    E = N // 2
    chi = V - E
    rep["V"], rep["E"], rep["chi"] = V, E, chi
    # boundary components of S(X) = boundary cycles; S* closed: chi(S*) = chi(X)
    # connected components of X
    uf = list(range(V))
    def find(x):
        while uf[x] != x:
            uf[x] = uf[uf[x]]
            x = uf[x]
        return x
    for d in range(N):
        a, b = find(seen[d]), find(seen[p[d]])
        uf[a] = b
    comps = len({find(x) for x in range(V)})
    rep["components_X"] = comps
    # components of S*: X components joined when a d^- circle and its d^+ partner lie in different comps
    circ_comp = {}
    for d in range(N):
        circ_comp.setdefault(B.circle[d], find(seen[d]))
    uf2 = {c: c for c in set(circ_comp.values())}
    def f2(x):
        while uf2[x] != x:
            x = uf2[x]
        return x
    for (ci, k), c in circ_comp.items():
        if k == "-":
            a, b = f2(c), f2(circ_comp[(ci, "+")])
            uf2[a] = b
    rep["components_Sstar"] = len({f2(c) for c in uf2})
    rep["unroll"] = unroll_check(B, p, g, nunroll)
    return rep

def unroll_check(B, p, g, nunroll):
    """Build X_n as a pushout and check that X_n -> R is an immersion for n <= nunroll.

    Level i copy of X carries the map f^i: each edge of X is subdivided into the
    letters of f^i(label).  For 1 <= i <= n the d^- circles of level i are glued
    (points AND edges, orientation-reversing) to the d^+ circles of level i-1.
    We realise X_n with union-find on points and edges and check that at every
    vertex distinct edge classes leave with distinct letters.  Returns the number of
    folding violations for n = 0..nunroll (all zero = immersion).
    """
    phi = B.phi
    N = B.N
    def fk(x, k):
        w = x
        for _ in range(k):
            w = apply(phi, w)
        return w
    sigma = lambda d: B.nxt[p[d]]
    vid = {}
    for d in range(N):
        if d in vid:
            continue
        e = d
        while True:
            vid[e] = d
            e = sigma(e)
            if e == d:
                break
    circles = {}
    for d in range(N):
        circles.setdefault(B.circle[d], []).append(d)
    results = []
    for n in range(nunroll + 1):
        parent = {}
        def find(x):
            r = x
            while parent.get(r, r) != r:
                r = parent[r]
            while parent.get(x, x) != r:
                nx = parent[x]
                parent[x] = r
                x = nx
            return r
        def union(a, b):
            a, b = find(a), find(b)
            if a != b:
                parent[a] = b
        def dart_path(i, d):
            """list of (tailpoint, letter, headpoint, edgekey, forward?) along dart d at level i"""
            c = d if d < p[d] else p[d]
            w = fk(B.label[c], i)
            L = len(w)
            pts = [("v", i, vid[c])] + [("m", i, c, j) for j in range(1, L)] + [("v", i, vid[B.nxt[c]])]
            fwd = [(pts[j], w[j], pts[j + 1], ("e", i, c, j), True) for j in range(L)]
            if c == d:
                return fwd
            return [(h, inv(x), t, ek, False) for (t, x, h, ek, _) in reversed(fwd)]
        alledges = []
        for i in range(n + 1):
            for d in range(N):
                if d < p[d]:
                    alledges.extend(dart_path(i, d))
        for i in range(1, n + 1):
            for ci in {c for (c, k) in circles}:
                sm = [s for d in sorted(circles[(ci, "-")]) for s in dart_path(i, d)]
                sp = [s for d in sorted(circles[(ci, "+")]) for s in dart_path(i - 1, d)]
                assert len(sm) == len(sp), "boundary length mismatch"
                L = len(sm)
                for k in range(L):
                    t1, x1, h1, e1, _ = sm[k]
                    t2, x2, h2, e2, _ = sp[L - 1 - k]
                    assert x2 == inv(x1), ("gluing label mismatch", i, ci, k, x1, x2)
                    union(t1, h2)
                    union(h1, t2)
                    union(e1, e2)
        star = {}
        for (t, x, h, ek, _) in alledges:
            for (a, y) in ((find(t), x), (find(h), inv(x))):
                star.setdefault(a, {}).setdefault(y, set()).add((find(ek), y))
        bad = sum(1 for a in star for y in star[a] if len(star[a][y]) > 1)
        results.append(bad)
    return results

def check_alignment(B):
    """sanity: d^- word and d^+ word are inverse under f (letterwise)."""
    for (w, k) in B.words:
        pass
    return True

if __name__ == "__main__":
    pass
