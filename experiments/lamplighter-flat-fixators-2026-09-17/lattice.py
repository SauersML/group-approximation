"""One-vertex cube complex lattices Lambda < Aut(T_a) x Aut(T_b) x Aut(T_c).
A solution (from cubesat.py) gives f_XY(x,y) = (y',x'):  x y = y' x'.
Letters are pairs (F, i), F in 'ABC', inverse (F, i^1)."""
import json, itertools

PAIRS = [('A', 'B'), ('A', 'C'), ('B', 'C')]

class Cube:
    def __init__(self, sol):
        self.n = dict(zip('ABC', sol['sizes']))
        self.sw = {}          # (X,x,Y,y) -> ((Y,y'),(X,x')) : "x y" = "y' x'"
        for X, Y in PAIRS:
            for k, (y2, x2) in sol[X + Y].items():
                x, y = map(int, k.split(','))
                self.sw[(X, x, Y, y)] = ((Y, y2), (X, x2))
                self.sw[(Y, y2, X, x2)] = ((X, x), (Y, y))   # "y' x'" = "x y"

    def normal(self, word, order):
        """Sort a word (list of letters) into blocks in the given factor order,
        freely reducing inside blocks.  Returns tuple of letters."""
        rank = {F: i for i, F in enumerate(order)}
        w = list(word)
        changed = True
        while changed:
            changed = False
            i = 0
            while i < len(w) - 1:
                (X, x), (Y, y) = w[i], w[i + 1]
                if X == Y and x == y ^ 1:
                    del w[i:i + 2]; changed = True; i = max(i - 1, 0); continue
                if rank[X] > rank[Y]:
                    p, q = self.sw[(X, x, Y, y)]
                    w[i], w[i + 1] = p, q; changed = True
                i += 1
        return tuple(w)

    def push(self, lam, x):
        """lam: tuple of letters of one factor, x a letter of another factor.
        lam x = x' lam' ; returns (x', lam')."""
        cur = x; out = []
        for l in reversed(lam):
            p, q = self.sw[(l[0], l[1], cur[0], cur[1])]
            cur = p; out.append(q)
        return cur, tuple(reversed(out))

    def words(self, F, L):
        n = self.n[F]
        if L == 0:
            yield (); return
        def rec(w):
            if len(w) == L:
                yield tuple(w); return
            for i in range(n):
                if w and w[-1][1] == i ^ 1:
                    continue
                w.append((F, i)); yield from rec(w); w.pop()
        yield from rec([])

    def cyc_reduced(self, F, L):
        for w in self.words(F, L):
            if L < 2 or w[0][1] != w[-1][1] ^ 1:
                yield w

    def level_perm(self, lam, Y, k):
        """permutation of lam (word in some factor) on reduced Y-words of length k"""
        pts = list(self.words(Y, k)); idx = {p: i for i, p in enumerate(pts)}
        perm = []
        for p in pts:
            st = lam; img = []
            for y in p:
                y2, st = self.push(st, y); img.append(y2)
            perm.append(idx[tuple(img)])
        return perm

    def fix_graph(self, lam, Y):
        """States reachable from lam while fixing Y-letters: dict state -> list of (y, state')"""
        G = {}; todo = [lam]
        while todo:
            s = todo.pop()
            if s in G:
                continue
            G[s] = []
            for i in range(self.n[Y]):
                y2, s2 = self.push(s, (Y, i))
                if y2 == (Y, i):
                    G[s].append((i, s2)); todo.append(s2)
        return G

    def pruned(self, lam, Y):
        """alive part of the fixed-vertex automaton: (succ restricted to alive, start or None)"""
        G = self.fix_graph(lam, Y)
        nodes = [(s, last) for s in G for last in list(range(self.n[Y])) + [None]]
        succ = {v: [(s2, i) for (i, s2) in G[v[0]] if v[1] is None or i != v[1] ^ 1] for v in nodes}
        alive = set(nodes)
        while True:
            dead = [v for v in alive if not any(w in alive for w in succ[v])]
            if not dead:
                break
            alive -= set(dead)
        succ = {v: [w for w in succ[v] if w in alive] for v in alive}
        start = (lam, None)
        return succ, (start if start in alive else None)

    def fix_counts(self, lam, Y, depth):
        """number of vertices at distance k in the pruned part of Fix_Y(lam)
        (vertices with an infinite fixed continuation), k=0..depth"""
        G = self.fix_graph(lam, Y)
        nodes = [(s, last) for s in G for last in list(range(self.n[Y])) + [None]]
        succ = {v: [(s2, i) for (i, s2) in G[v[0]] if v[1] is None or i != v[1] ^ 1] for v in nodes}
        alive = set(nodes)
        while True:
            dead = [v for v in alive if not any(w in alive for w in succ[v])]
            if not dead:
                break
            alive -= set(dead)
        start = (lam, None)
        if start not in alive:
            return [1] + [0] * depth
        cnt = {start: 1}; res = [1]
        for _ in range(depth):
            nc = {}
            for v, c in cnt.items():
                for w in succ[v]:
                    if w in alive:
                        nc[w] = nc.get(w, 0) + c
            cnt = nc; res.append(sum(nc.values()))
        return res

def load(path, idx=0):
    with open(path) as f:
        lines = [l for l in f if l.startswith('{')]
    return Cube(json.loads(lines[idx]))
