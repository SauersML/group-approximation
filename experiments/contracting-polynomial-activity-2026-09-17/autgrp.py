"""Small automaton-group toolkit: nucleus search, activity degree, word test.

Conventions: X = {0..d-1}. A state is (perm, children) with perm a tuple
(perm[x] = image of letter x) and children[x] = section at x (state index).
Elements are words (s1,...,sk) meaning s1 s2 ... sk acting on the left, so sk
acts first; (gh)|_x = g|_{h(x)} h|_x.
"""
import sys
from collections import defaultdict

class Automaton:
    def __init__(self, d, states, names=None):
        # states: list of (perm, children); state 0 must be the identity.
        self.d = d
        self.perm = [tuple(p) for p, c in states]
        self.child = [tuple(c) for p, c in states]
        self.names = names or [str(i) for i in range(len(states))]
        n = len(states)
        # add inverses
        self.inv = [None] * n
        for s in range(n):
            if self.perm[s] == tuple(range(d)) and all(c == 0 for c in self.child[s]):
                self.inv[s] = s
        self.inv[0] = 0
        base = n
        todo = [s for s in range(n) if self.inv[s] is None]
        idx = {}
        for s in todo:
            idx[s] = base + len(idx)
        for s in todo:
            p = self.perm[s]
            pinv = [0] * d
            for x in range(d):
                pinv[p[x]] = x
            # s^{-1}|_y = (s|_{s^{-1}(y)})^{-1}
            ch = []
            for y in range(d):
                c = self.child[s][pinv[y]]
                ch.append(c if self.inv[c] == c and c in (0,) else None)
            self.perm.append(tuple(pinv))
            self.child.append(None)
            self.names.append(self.names[s] + "'")
            self.inv[s] = idx[s]
        while len(self.inv) < len(self.perm):
            self.inv.append(None)
        for s in todo:
            t = idx[s]
            self.inv[t] = s
        for s in todo:
            t = idx[s]
            pinv = self.perm[t]
            ch = []
            for y in range(d):
                c = self.child[s][pinv[y]]
                ch.append(self.inv[c])
            self.child[t] = tuple(ch)
        self.nstates = len(self.perm)

    def reduce(self, w):
        out = []
        for s in w:
            if s == 0:
                continue
            if out and self.inv[out[-1]] == s:
                out.pop()
            else:
                out.append(s)
        return tuple(out)

    def act(self, w):
        """return (perm, children words) of word w."""
        d = self.d
        perm = []
        kids = []
        for x in range(d):
            y = x
            sec = []
            for s in reversed(w):
                sec.append(self.child[s][y])
                y = self.perm[s][y]
            perm.append(y)
            kids.append(self.reduce(tuple(reversed(sec))))
        return tuple(perm), kids


class Universe:
    """Set of words closed under sections, with Moore-machine minimization."""
    def __init__(self, A):
        self.A = A
        self.id = {}
        self.words = []
        self.perm = []
        self.kids = []
        self.cls = None
        self.add(())

    def add(self, w):
        w = self.A.reduce(w)
        if w in self.id:
            return self.id[w]
        stack = [w]
        self.id[w] = len(self.words); self.words.append(w); self.perm.append(None); self.kids.append(None)
        while stack:
            u = stack.pop()
            p, ks = self.A.act(u)
            i = self.id[u]
            self.perm[i] = p
            kid_ids = []
            for k in ks:
                if k not in self.id:
                    self.id[k] = len(self.words); self.words.append(k); self.perm.append(None); self.kids.append(None)
                    stack.append(k)
                kid_ids.append(self.id[k])
            self.kids[i] = tuple(kid_ids)
            if len(self.words) > 3_000_000:
                raise MemoryError("universe too big")
        self.cls = None
        return self.id[w]

    def refine(self):
        n = len(self.words)
        lab = {}
        c = [lab.setdefault(self.perm[i], len(lab)) for i in range(n)]
        while True:
            lab = {}
            c2 = [lab.setdefault((c[i],) + tuple(c[k] for k in self.kids[i]), len(lab)) for i in range(n)]
            if len(lab) == len(set(c)):
                break
            c = c2
        self.cls = c2
        return c2

    def cl(self, w):
        i = self.add(w)
        if self.cls is None:
            self.refine()
        return self.cls[i]


def sccs(nodes, succ):
    """Tarjan; returns list of SCCs (lists)."""
    index = {}; low = {}; st = []; on = set(); out = []; cnt = [0]
    sys.setrecursionlimit(1000000)
    def strong(v):
        index[v] = low[v] = cnt[0]; cnt[0] += 1; st.append(v); on.add(v)
        for w in succ(v):
            if w not in index:
                strong(w); low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == v:
                    break
            out.append(comp)
    for v in nodes:
        if v not in index:
            strong(v)
    return out


def class_graph(U, words):
    """classes reachable from the given words, with a representative word and successor classes."""
    if U.cls is None:
        U.refine()
    rep = {}
    succ = {}
    stack = []
    for w in words:
        i = U.add(w)
    U.refine()
    for w in words:
        i = U.id[U.A.reduce(w)]
        c = U.cls[i]
        if c not in rep:
            rep[c] = i; stack.append(c)
    while stack:
        c = stack.pop()
        i = rep[c]
        ss = []
        for k in U.kids[i]:
            ck = U.cls[k]
            ss.append(ck)
            if ck not in rep:
                rep[ck] = k; stack.append(ck)
        succ[c] = ss
    return rep, succ


def core(U, words):
    rep, succ = class_graph(U, words)
    comps = sccs(list(rep), lambda c: succ[c])
    cor = set()
    for comp in comps:
        if len(comp) > 1 or comp[0] in succ[comp[0]]:
            cor.update(comp)
    # close the core under sections: the nucleus is reachable from cycles
    stack = list(cor)
    while stack:
        c = stack.pop()
        for x in succ[c]:
            if x not in cor:
                cor.add(x); stack.append(x)
    return {c: U.words[rep[c]] for c in cor}, rep, succ


def nucleus(A, max_size=400, verbose=False):
    U = Universe(A)
    gens = [(s,) for s in range(A.nstates)]
    N, _, _ = core(U, gens)
    for it in range(60):
        prods = [U.A.reduce(a + b) for a in N.values() for b in N.values()]
        C, _, _ = core(U, list(N.values()) + prods)
        # classes may be renumbered after refinement: recompute N classes
        Nw = {U.cls[U.id[w]]: w for w in N.values()}
        new = {c: w for c, w in C.items() if c not in Nw}
        if verbose:
            print("iter", it, "|N|", len(Nw), "new", len(new), file=sys.stderr)
        if not new:
            return Nw, U
        Nw.update(new)
        N = Nw
        if len(N) > max_size:
            return None, U
    return None, U


def activity_degree(A):
    """Sidki degree of the (minimized) generating automaton; None if exponential."""
    U = Universe(A)
    words = [(s,) for s in range(A.nstates)]
    rep, succ = class_graph(U, words)
    triv = U.cls[U.id[()]]
    nodes = [c for c in rep if c != triv]
    sub = lambda c: [x for x in succ[c] if x != triv]
    comps = sccs(nodes, sub)
    comp_of = {}
    circ = []
    for k, comp in enumerate(comps):
        for c in comp:
            comp_of[c] = k
        edges = sum(1 for c in comp for x in sub(c) if comp_of.get(x, -1) == k or x in comp)
        cyc = len(comp) > 1 or comp[0] in sub(comp[0])
        if cyc:
            e = sum(1 for c in comp for x in sub(c) if x in comp)
            if e != len(comp):
                return None, rep
        circ.append(cyc)
    # longest chain of circuits in condensation DAG
    memo = {}
    def depth(k):
        if k in memo:
            return memo[k]
        best = 0
        for c in comps[k]:
            for x in sub(c):
                kk = comp_of[x]
                if kk != k:
                    best = max(best, depth(kk))
        memo[k] = best + (1 if circ[k] else 0)
        return memo[k]
    deg = {}
    for k in range(len(comps)):
        for c in comps[k]:
            deg[c] = depth(k) - 1
    return deg, rep


def fix_inverses(A):
    """Point inv[s] to the lowest-index state equal to s^{-1} (so reduce cancels them)."""
    U = Universe(A)
    for s in range(A.nstates):
        for s2 in range(A.nstates):
            U.add((s, s2))
    U.refine()
    one = U.cls[U.id[()]]
    for s in range(A.nstates):
        for s2 in range(A.nstates):
            if U.cls[U.id[A.reduce((s, s2))]] == one or (s, s2) == (0, 0):
                A.inv[s] = s2
                break
    return A
