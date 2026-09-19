#!/usr/bin/env python3
"""Loop graphs of unit-weight recursions (library for `unit-weight-stable-relators-are-loop-graph-words`).

A recursion has rooted letters (a root permutation, all sections empty) and state letters
(a root permutation and letter sections, words with at most one state letter: unit weight).
Right actions: (uv)|_x = u|_x v|_{x^u}.  Points 0..N-1.  Words are tuples of (letter, +-1).

Level-n loop graph Delta_n.  A loop state is (s, eps, y) with y in X^n and s^eps|_y = a s^eps b
(a, b rooted words).  It is an edge  iota = y^{a^-1}  ->  o = y^{s^eps b}  labelled a s^eps b.
The inverse edge is the loop state of s^-eps at y^{s^eps}.  Lemma A: a reduced word u satisfies
u|_v = u (|v| = n) iff u is the label of a reduced closed path at v in Delta_n.
"""
import itertools

N = 11
def perm_from_cycles(cycles, n=N):
    p = list(range(n))
    for c in cycles:
        for i, x in enumerate(c):
            p[x] = c[(i + 1) % len(c)]
    return tuple(p)
ID = tuple(range(N))
def pmul(p, q):  # first p then q
    return tuple(q[p[x]] for x in range(len(p)))
def pinv(p):
    r = [0] * len(p)
    for x in range(len(p)): r[p[x]] = x
    return tuple(r)
ALPHA = perm_from_cycles([list(range(11))])
BETA = perm_from_cycles([[0, 1, 2, 3, 7], [4, 9, 6, 10, 5]])

def W(s):  # "b A a" -> word; capital = inverse
    return tuple((t.lower(), -1 if t[0].isupper() else 1) for t in s.split())
def reduce(w):
    st = []
    for l in w:
        if st and st[-1][0] == l[0] and st[-1][1] == -l[1]: st.pop()
        else: st.append(l)
    return tuple(st)
def inv(w): return tuple((l, -e) for l, e in reversed(w))
def fmt(u): return " ".join(l if e == 1 else l.upper() for l, e in u) or "1"

class Rec:
    def __init__(self, name, rooted, states):
        """rooted: {letter: perm}; states: {letter: (perm, {x: word})}"""
        self.name, self.rooted, self.states = name, rooted, states
    def is_state(self, l): return l in self.states
    def lperm(self, l, e):
        p = self.rooted[l] if l in self.rooted else self.states[l][0]
        return p if e == 1 else pinv(p)
    def lsec(self, l, e, x):
        if l in self.rooted: return ()
        if e == 1: return self.states[l][1].get(x, ())
        y = pinv(self.states[l][0])[x]
        return inv(self.states[l][1].get(y, ()))
    def perm(self, w):
        p = ID
        for l, e in w: p = pmul(p, self.lperm(l, e))
        return p
    def sec(self, w, x):
        out = []
        for l, e in w:
            out.extend(self.lsec(l, e, x)); x = self.lperm(l, e)[x]
        return reduce(out)
    def secv(self, w, y):
        for x in y: w = self.sec(w, x)  # y read top-down; each step the section at the point
        return w
    def act(self, w, y):  # level-|y| action on the tuple y
        y = list(y)
        for l, e in w:
            if not y: break
            y = self._act_letter(l, e, y)
        return tuple(y)
    def _act_letter(self, l, e, y):
        out, w = [], ((l, e),)
        for x in y:
            if not w: out.append(x); continue
            out.append(self.perm(w)[x]); w = self.sec(w, x)
        return out
    def weight(self, w): return sum(1 for l, _ in w if self.is_state(l))
    def unit_weight(self):
        return all(self.weight(w) <= 1 for _, secs in self.states.values() for w in secs.values())
    def trivial(self, w, cap=400000):
        seen, todo = set(), [reduce(w)]
        while todo:
            u = todo.pop()
            if u in seen or not u: continue
            seen.add(u)
            if self.perm(u) != ID: return False
            if len(seen) > cap: raise RuntimeError("closure too large")
            for x in range(N): todo.append(self.sec(u, x))
        return True
    def order(self, w, bound=240):
        """exact order <= bound, else None.  Finite order o is certified by trivial(w^o)."""
        p = self.perm(w); k0 = 1
        while p != ID and k0 <= bound:  # the order is a multiple of the root order
            k0 += 1; p = pmul(p, self.perm(w))
        r = self.perm(w); ordr = 1; q = r
        while q != ID: q = pmul(q, r); ordr += 1
        for j in range(ordr, bound + 1, ordr):
            if self.trivial(w * j): return j
        return None
    def closure(self, words, cap=200000):
        seen, todo = set(), [reduce(w) for w in words]
        while todo:
            u = todo.pop()
            if u in seen or not u: continue
            seen.add(u)
            if len(seen) > cap: raise RuntimeError("closure too large")
            for x in range(N): todo.append(self.sec(u, x))
        return seen

    # ---- loop graph ------------------------------------------------------------------
    def loop_states(self, n):
        """all (s, eps, y, a, b) with |y| = n and s^eps|_y = a s^eps b, a, b rooted"""
        out = []
        for s in self.states:
            for e in (1, -1):
                frontier = [((), ((s, e),))]
                for _ in range(n):
                    nxt = []
                    for y, w in frontier:
                        for x in range(N):
                            u = self.sec(w, x)
                            if self.weight(u) == 1: nxt.append((y + (x,), u))
                    frontier = nxt
                for y, u in frontier:
                    i = [k for k, (l, _) in enumerate(u) if self.is_state(l)][0]
                    if u[i] == (s, e): out.append((s, e, y, u[:i], u[i + 1:]))
        return out
    def loop_graph(self, n):
        edges = []
        for s, e, y, a, b in self.loop_states(n):
            iota = self.act(inv(a), y); o = self.act(((s, e),) + b, y)
            edges.append((iota, o, a + ((s, e),) + b, (s, e, y)))
        return edges

def components(edges):
    """union-find over the undirected graph given by the positive edges; returns list of
    (vertices, positive edges, rank, cycle words at a base vertex)"""
    pos = [ed for ed in edges if ed[3][1] == 1]
    par = {}
    def f(x):
        par.setdefault(x, x)
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for i, o, _, _ in pos: par[f(i)] = f(o)
    comps = {}
    for ed in pos: comps.setdefault(f(ed[0]), []).append(ed)
    out = []
    for root, E in comps.items():
        V = sorted({v for ed in E for v in ed[:2]})
        base = V[0]
        # spanning tree by BFS; path word from base to each vertex
        adj = {}
        for k, (i, o, lab, _) in enumerate(E):
            adj.setdefault(i, []).append((o, lab, k)); adj.setdefault(o, []).append((i, inv(lab), k))
        pw, tree, todo = {base: ()}, set(), [base]
        while todo:
            v = todo.pop()
            for wv, lab, k in adj.get(v, []):
                if wv not in pw: pw[wv] = reduce(pw[v] + lab); tree.add(k); todo.append(wv)
        cyc = [reduce(pw[i] + lab + inv(pw[o])) for k, (i, o, lab, _) in enumerate(E) if k not in tree]
        out.append((V, E, len(E) - len(V) + 1, base, cyc))
    return out
