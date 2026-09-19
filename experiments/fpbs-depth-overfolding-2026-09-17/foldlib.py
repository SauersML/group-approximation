"""Stallings folds over a finite F(a,b)-set Q, depth-j coset graphs, and
fold closures of vertex merges.

Conventions.
- Q = {0..n-1} with a right action given by permutations PA, PB:
  p.a = PA[p], p.b = PB[p].
- Words are lists of (letter, e) with letter in 'ab', e = +1/-1.
- phi: a -> a, b -> b a b^-1 b^-1.  t_j = phi^j(b), L_j = <a, t_j>.
- Gamma_M(Q) = Stallings fold of: real vertices Q, and for each p in Q and
  each generator w of M a path labelled w from p to p.w.
"""
import random


def inv(w):
    return [(l, -e) for (l, e) in reversed(w)]


def reduce(w):
    out = []
    for x in w:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
            out.pop()
        else:
            out.append(x)
    return out


A = [('a', 1)]
B = [('b', 1)]


def phi(w):
    out = []
    for (l, e) in w:
        img = A if l == 'a' else B + A + inv(B) + inv(B)
        out += img if e == 1 else inv(img)
    return reduce(out)


def t(j):
    w = B
    for _ in range(j):
        w = phi(w)
    return w


def act(p, w, PA, PB, IA, IB):
    for (l, e) in w:
        if l == 'a':
            p = PA[p] if e == 1 else IA[p]
        else:
            p = PB[p] if e == 1 else IB[p]
    return p


class Fold:
    """Union-find folded graph.  out[r][(l,e)] = target root."""

    def __init__(self):
        self.par = []
        self.adj = []  # dict (l,e) -> vertex

    def new(self):
        self.par.append(len(self.par))
        self.adj.append({})
        return len(self.par) - 1

    def find(self, x):
        while self.par[x] != x:
            self.par[x] = self.par[self.par[x]]
            x = self.par[x]
        return x

    def add_edge(self, u, l, v):
        self._pending = getattr(self, '_pending', [])
        self._link(u, (l, 1), v)
        self._link(v, (l, -1), u)
        self.fold()

    def _link(self, u, k, v):
        u = self.find(u)
        d = self.adj[u]
        if k in d:
            self._pending.append((d[k], v))
        else:
            d[k] = v

    def union(self, x, y):
        self._pending = getattr(self, '_pending', [])
        self._pending.append((x, y))
        self.fold()

    def fold(self):
        while self._pending:
            x, y = self._pending.pop()
            x, y = self.find(x), self.find(y)
            if x == y:
                continue
            if len(self.adj[x]) < len(self.adj[y]):
                x, y = y, x
            self.par[y] = x
            for k, v in self.adj[y].items():
                if k in self.adj[x]:
                    self._pending.append((self.adj[x][k], v))
                else:
                    self.adj[x][k] = v
            self.adj[y] = {}

    def add_path(self, u, w, v):
        cur = u
        for i, (l, e) in enumerate(w):
            nxt = v if i == len(w) - 1 else self.new()
            if e == 1:
                self.add_edge(cur, l, nxt)
            else:
                self.add_edge(nxt, l, cur)
            cur = nxt

    def roots(self):
        return sorted({self.find(x) for x in range(len(self.par))})

    def step(self, r, k):
        v = self.adj[self.find(r)].get(k)
        return None if v is None else self.find(v)


def inverse_perm(P):
    I = [0] * len(P)
    for i, x in enumerate(P):
        I[x] = i
    return I


def random_q(n, rng):
    PA = list(range(n)); rng.shuffle(PA)
    PB = list(range(n)); rng.shuffle(PB)
    return PA, PB


def gamma(PA, PB, gens):
    """Fold of Q with generator paths.  Returns (Fold, list of roots)."""
    n = len(PA)
    IA, IB = inverse_perm(PA), inverse_perm(PB)
    F = Fold()
    for _ in range(n):
        F.new()
    for p in range(n):
        for w in gens:
            F.add_path(p, w, act(p, w, PA, PB, IA, IB))
    return F


class Graph:
    """A frozen folded graph: vertices 0..V-1, reals 0..n-1 (vertex p = real p),
    nb[v][k] = neighbour, over[v] = point of Q under v."""

    def __init__(self, F, n, PA, PB):
        roots = F.roots()
        idx = {}
        # reals first, in order
        for p in range(n):
            idx[F.find(p)] = p
        for r in roots:
            if r not in idx:
                idx[r] = len(idx)
        assert len({F.find(p) for p in range(n)}) == n, 'reals merged'
        self.V = len(idx)
        self.n = n
        self.nb = [dict() for _ in range(self.V)]
        for r in roots:
            for k, v in F.adj[r].items():
                self.nb[idx[r]][k] = idx[F.find(v)]
        # over map by BFS from reals
        IA, IB = inverse_perm(PA), inverse_perm(PB)
        self.over = [None] * self.V
        self.word = [None] * self.V
        from collections import deque
        dq = deque()
        for p in range(n):
            self.over[p] = p
            self.word[p] = (p, [])
            dq.append(p)
        while dq:
            v = dq.popleft()
            for k, u in self.nb[v].items():
                if self.over[u] is None:
                    self.over[u] = act(self.over[v], [k], PA, PB, IA, IB)
                    self.word[u] = (self.word[v][0], self.word[v][1] + [k])
                    dq.append(u)
        assert all(o is not None for o in self.over)

    def read(self, v, w):
        for k in w:
            v = self.nb[v].get(k)
            if v is None:
                return None
        return v


def depth_graphs(PA, PB, j):
    n = len(PA)
    Gj = Graph(gamma(PA, PB, [A, t(j)]), n, PA, PB)
    Gj1 = Graph(gamma(PA, PB, [A, t(j + 1)]), n, PA, PB)
    # map Gj1 -> Gj by reading the BFS word from the real start
    m = [None] * Gj1.V
    for v in range(Gj1.V):
        p, w = Gj1.word[v]
        m[v] = Gj.read(p, w)
        assert m[v] is not None
    return Gj, Gj1, m


def closure(G, pairs):
    """Fold closure of merges on the folded graph G.  Returns class labels."""
    par = list(range(G.V))
    size = [1] * G.V
    cadj = [dict(G.nb[v]) for v in range(G.V)]

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    stack = list(pairs)
    while stack:
        x, y = stack.pop()
        x, y = find(x), find(y)
        if x == y:
            continue
        if size[x] < size[y]:
            x, y = y, x
        par[y] = x
        size[x] += size[y]
        for k, v in cadj[y].items():
            if k in cadj[x]:
                stack.append((cadj[x][k], v))
            else:
                cadj[x][k] = v
        cadj[y] = None
    return [find(v) for v in range(G.V)]


def contains_kernel(G, cls, m):
    """Does the partition cls (list of labels) contain ker(m)?"""
    first = {}
    for v in range(G.V):
        key = m[v]
        if key in first:
            if cls[first[key]] != cls[v]:
                return False
        else:
            first[key] = v
    return True


def equals_kernel(G, cls, m):
    if not contains_kernel(G, cls, m):
        return False
    first = {}
    for v in range(G.V):
        c = cls[v]
        if c in first:
            if m[first[c]] != m[v]:
                return False
        else:
            first[c] = v
    return True
