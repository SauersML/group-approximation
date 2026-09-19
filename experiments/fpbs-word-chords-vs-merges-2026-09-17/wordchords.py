"""Word chords versus vertex merges for the relative rank d(Q).

Setting (fpbs-profinite-relcost-equals-relative-rank-gradient): L = F(a,b)
acts on the right on Q = {0..n-1} by permutations PA, PB; K = <a, c>,
c = b a b^-1 b^-1.  Gamma_A is the Stallings-folded K-graph over Q (real
vertices Q, an a-edge p -> p.a and a c-path at every p).  When K is
transitive on Q, Gamma_A is the core graph of A = Stab_K(q) inside
L = F(a,b), and d(Q) = rk(Stab_L(q) : A) is the least number of chords
(p, w) whose paths, added to Gamma_A and folded, give exactly n vertices.

rho(Q) is the least number of vertex MERGES (identify two vertices of the
current folded graph lying over the same point of Q) needed to reach n
vertices.  Always d(Q) <= rho(Q), since a merge is the chord read along a
path of Gamma_A.  The census numbers in the relative-rank and congruence
experiments are greedy upper bounds on rho, not on d.

This script asks whether chords that are NOT merges (reduced arcs that stay
outside Gamma_A until they meet other arcs) can do better.  A reduced arc
is (u, w, v): u, v vertices of the folded graph, w a reduced word with
phi(u).w = phi(v), first letter of w missing at u, inverse of the last
letter missing at v.  Every chord is a merge or, after folding its ends
into the graph, a reduced arc (the graph is connected).

Letters: 0=a, 1=A, 2=b, 3=B; inverse is l ^ 1.
"""
import itertools
import random
import sys
from collections import defaultdict


class Folder:
    __slots__ = ('par', 'out', 'phi', 'real', '_pending')

    def __init__(self):
        self.par = []
        self.out = []
        self.phi = []
        self.real = []
        self._pending = []

    def clone(self):
        G = Folder()
        G.par = self.par[:]
        G.out = [dict(d) for d in self.out]
        G.phi = self.phi[:]
        G.real = self.real[:]
        return G

    def new(self, phi, real=False):
        self.par.append(len(self.par))
        self.out.append({})
        self.phi.append(phi)
        self.real.append(real)
        return len(self.par) - 1

    def find(self, v):
        par = self.par
        r = v
        while par[r] != r:
            r = par[r]
        while par[v] != r:
            par[v], v = r, par[v]
        return r

    def _run(self):
        pend = self._pending
        while pend:
            item = pend.pop()
            if item[0] == 'm':
                self._merge(item[1], item[2])
                continue
            _, u, l, v = item
            u = self.find(u)
            v = self.find(v)
            for (x, lab, y) in ((u, l, v), (v, l ^ 1, u)):
                t = self.out[x].get(lab)
                if t is None:
                    self.out[x][lab] = y
                else:
                    t = self.find(t)
                    if t != y:
                        pend.append(('m', t, y))

    def _merge(self, u, v):
        u = self.find(u)
        v = self.find(v)
        if u == v:
            return
        assert self.phi[u] == self.phi[v], 'phi mismatch'
        if len(self.out[u]) < len(self.out[v]):
            u, v = v, u
        self.par[v] = u
        self.real[u] = self.real[u] or self.real[v]
        for lab, t in self.out[v].items():
            s = self.out[u].get(lab)
            if s is None:
                self.out[u][lab] = t
            else:
                x, y = self.find(s), self.find(t)
                if x != y:
                    self._pending.append(('m', x, y))
        self.out[v] = {}

    def edge(self, u, l, v):
        self._pending.append(('e', u, l, v))

    def merge(self, u, v):
        self._pending.append(('m', u, v))
        self._run()

    def roots(self):
        return [v for v in range(len(self.par)) if self.par[v] == v]

    def nroots(self):
        return sum(1 for v in range(len(self.par)) if self.par[v] == v)

    def add_arc(self, u, word, v, tab):
        """Attach a path labelled word from u to v (phi-compatible) and fold."""
        cur = u
        x = self.phi[u]
        for i, l in enumerate(word):
            x = tab[l][x]
            if i == len(word) - 1:
                nxt = v
                assert self.phi[v] == x, 'arc endpoint mismatch'
            else:
                nxt = self.new(x)
            self.edge(cur, l, nxt)
            cur = nxt
        self._run()


def tables(PA, PB):
    n = len(PA)
    IA = [0] * n
    IB = [0] * n
    for i, x in enumerate(PA):
        IA[x] = i
    for i, x in enumerate(PB):
        IB[x] = i
    return [PA, IA, PB, IB]


def build_gamma_k(PA, PB):
    tab = tables(PA, PB)
    PA_, IA, PB_, IB = tab
    n = len(PA)
    F = Folder()
    for p in range(n):
        F.new(p, True)
    for p in range(n):
        F.edge(p, 0, PA[p])
        pb = PB[p]
        pba = PA[pb]
        pbaB = IB[pba]
        pc = IB[pbaB]
        x1 = F.new(pb)
        x2 = F.new(pba)
        x3 = F.new(pbaB)
        F.edge(p, 2, x1)
        F.edge(x1, 0, x2)
        F.edge(x3, 2, x2)
        F.edge(pc, 2, x3)
    F._run()
    return F, tab


def orbits_count(n, moves):
    seen = [False] * n
    cnt = 0
    for s in range(n):
        if seen[s]:
            continue
        cnt += 1
        st = [s]
        seen[s] = True
        while st:
            p = st.pop()
            for mv in moves:
                q = mv(p)
                if not seen[q]:
                    seen[q] = True
                    st.append(q)
    return cnt


def random_q(n, rng):
    """Random L-set with L and K transitive (K-orbits counted with inverses)."""
    while True:
        PA = list(range(n))
        rng.shuffle(PA)
        PB = list(range(n))
        rng.shuffle(PB)
        PA_, IA, PB_, IB = tables(PA, PB)
        c = lambda p: IB[IB[PA[PB[p]]]]
        cinv = lambda p: IB[IA[PB[PB[p]]]]
        if orbits_count(n, [lambda p: PA[p], lambda p: IA[p], c, cinv]) == 1:
            return PA, PB


def merge_pairs(F):
    over = defaultdict(list)
    for r in F.roots():
        over[F.phi[r]].append(r)
    out = []
    for p, L in over.items():
        for u, v in itertools.combinations(L, 2):
            out.append((u, v))
    return out


def signature(F, N):
    lab = {}
    sig = []
    for v in range(N):
        r = F.find(v)
        if r not in lab:
            lab[r] = len(lab)
        sig.append(lab[r])
    return tuple(sig)


def rho_exact(F, n, maxdepth):
    """Least number of merges reaching n vertices, or None if > maxdepth."""
    N0 = len(F.par)
    if F.nroots() == n:
        return 0
    frontier = {signature(F, N0): F}
    for depth in range(1, maxdepth + 1):
        nxt = {}
        for G in frontier.values():
            for (u, v) in merge_pairs(G):
                H = G.clone()
                H.merge(u, v)
                if H.nroots() == n:
                    return depth
                s = signature(H, N0)
                if s not in nxt:
                    nxt[s] = H
        frontier = nxt
    return None


def reduced_words(maxlen):
    out = []
    def rec(w):
        if w:
            out.append(tuple(w))
        if len(w) == maxlen:
            return
        for l in range(4):
            if w and l == (w[-1] ^ 1):
                continue
            w.append(l)
            rec(w)
            w.pop()
    rec([])
    return out


def reduced_arcs(F, tab, maxlen):
    """All reduced arcs (u, w, v) with |w| <= maxlen."""
    roots = F.roots()
    over = defaultdict(list)
    for r in roots:
        over[F.phi[r]].append(r)
    words = reduced_words(maxlen)
    arcs = []
    for u in roots:
        miss = [l for l in range(4) if l not in F.out[u]]
        if not miss:
            continue
        x0 = F.phi[u]
        for w in words:
            if w[0] not in F.out[u]:
                x = x0
                for l in w:
                    x = tab[l][x]
                last_inv = w[-1] ^ 1
                for v in over[x]:
                    if last_inv not in F.out[v]:
                        if len(w) == 1 and (v, last_inv, u) > (u, w[0], v):
                            pass
                        arcs.append((u, w, v))
    return arcs


def arc_ports(arc):
    u, w, v = arc
    return ((u, w[0]), (v, w[-1] ^ 1))


def restricted_relation(G, N0):
    """Partition of the original Gamma_A vertices induced by G."""
    return signature(G, N0)


def pairs_closure_count(F, n, target_sig, N0, maxk):
    """Least k <= maxk such that k merges give a relation containing target."""
    # target classes
    cls = defaultdict(list)
    for v, s in enumerate(target_sig):
        cls[s].append(v)
    def contains(G):
        for L in cls.values():
            r = G.find(L[0])
            for v in L[1:]:
                if G.find(v) != r:
                    return False
        return True
    if contains(F):
        return 0
    frontier = {signature(F, N0): F}
    for depth in range(1, maxk + 1):
        nxt = {}
        for G in frontier.values():
            for (u, v) in merge_pairs(G):
                H = G.clone()
                H.merge(u, v)
                if contains(H):
                    return depth
                s = signature(H, N0)
                if s not in nxt:
                    nxt[s] = H
        frontier = nxt
    return None
