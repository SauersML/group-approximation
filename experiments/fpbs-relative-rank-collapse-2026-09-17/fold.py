"""Stallings folding test for the relative rank of Stab_L(q) over Stab_K(q).

L = F(a, b) acts on the right on a finite set Q = {0..n-1} by permutations
PA (letter a) and PB (letter b).  K = <a, c>, c = b a b^-1 b^-1.

Gamma_K: the labelled graph with an a-edge p -> p.a and a c-path
p -b-> x1 -a-> x2 -B-> x3 -B-> p.c at every real vertex p.  After Stallings
folding, a real vertex p has a b-edge to a real vertex iff (x, x.b) lies in
E_K on every free action with Q as a factor.  Identifying an extra vertex u
with the real vertex phi(u) is the effect of one chord edge (label = label of
a path from a real vertex to u).  The folded graph has exactly n vertices iff
the chords together with K generate E_L on every free cover of Q.
Letters: 0=a, 1=A, 2=b, 3=B; inverse is l ^ 1.
"""
import random, sys


class Folder:
    def __init__(self):
        self.par = []
        self.out = []   # dict label -> vertex (not necessarily root)
        self.phi = []
        self.real = []

    def new(self, phi, real):
        self.par.append(len(self.par)); self.out.append({})
        self.phi.append(phi); self.real.append(real)
        return len(self.par) - 1

    def find(self, v):
        par = self.par
        while par[v] != v:
            par[v] = par[par[v]]; v = par[v]
        return v

    def edge(self, u, l, v):
        self._pending = [(u, l, v)]
        self._run()

    def _run(self):
        pend = self._pending
        while pend:
            item = pend.pop()
            if item[0] == 'm':
                self._merge(item[1], item[2]); continue
            u, l, v = item
            u = self.find(u); v = self.find(v)
            for (x, lab, y) in ((u, l, v), (v, l ^ 1, u)):
                t = self.out[x].get(lab)
                if t is None:
                    self.out[x][lab] = y
                else:
                    t = self.find(t)
                    if t != y:
                        pend.append(('m', t, y))

    def _merge(self, u, v):
        u = self.find(u); v = self.find(v)
        if u == v:
            return
        assert self.phi[u] == self.phi[v], "phi mismatch"
        if len(self.out[u]) < len(self.out[v]):
            u, v = v, u
        # keep u; if v real keep realness
        self.par[v] = u
        self.real[u] = self.real[u] or self.real[v]
        for lab, t in self.out[v].items():
            s = self.out[u].get(lab)
            if s is None:
                self.out[u][lab] = t
            else:
                a, b = self.find(s), self.find(t)
                if a != b:
                    self._pending.append(('m', a, b))
        self.out[v] = {}

    def merge(self, u, v):
        self._pending = [('m', u, v)]
        self._run()

    def roots(self):
        return {self.find(v) for v in range(len(self.par))}


def act(P, p, word):
    PA, PB = P
    IA = [0] * len(PA); IB = [0] * len(PB)
    for i, x in enumerate(PA): IA[x] = i
    for i, x in enumerate(PB): IB[x] = i
    tab = [PA, IA, PB, IB]
    for l in word:
        p = tab[l][p]
    return p


def build_gamma_k(PA, PB):
    n = len(PA)
    IB = [0] * n
    for i, x in enumerate(PB): IB[x] = i
    F = Folder()
    for p in range(n):
        F.new(p, True)
    F._pending = []
    for p in range(n):
        F._pending.append((p, 0, PA[p]))
        pb = PB[p]; pba = PA[pb]; pbaB = IB[pba]; pc = IB[pbaB]
        x1 = F.new(pb, False); x2 = F.new(pba, False); x3 = F.new(pbaB, False)
        F._pending += [(p, 2, x1), (x1, 0, x2), (x3, 2, x2), (pc, 2, x3)]
    F._run()
    return F


def extras(F):
    return [r for r in F.roots() if not F.real[r]]


def ncls(F):
    return len(F.roots())


def k_orbits(PA, PB):
    n = len(PA)
    IB = [0] * n
    for i, x in enumerate(PB): IB[x] = i
    seen = [False] * n; cnt = 0
    for s in range(n):
        if seen[s]: continue
        cnt += 1; st = [s]; seen[s] = True
        while st:
            p = st.pop()
            c = IB[IB[PA[PB[p]]]]
            for q in (PA[p], c):
                if not seen[q]: seen[q] = True; st.append(q)
        # inverse moves are covered since orbits of a permutation group on a finite set
    return cnt


def random_perm(n, rng):
    p = list(range(n)); rng.shuffle(p); return p


def collapse_count(PA, PB, rng, strategy='random'):
    """Number of identifications (chord edges) until the folded graph has n vertices."""
    import copy
    F = build_gamma_k(PA, PB)
    n = len(PA)
    count = 0
    hist = [ncls(F) - n]
    while ncls(F) > n:
        ex = extras(F)
        if strategy == 'random':
            u = rng.choice(ex)
        else:
            u = ex[0]
        F.merge(u, F.phi[u])  # real vertex with index phi[u]
        count += 1
        hist.append(ncls(F) - n)
    return count, hist


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    for t in range(trials):
        PA = random_perm(n, rng); PB = random_perm(n, rng)
        c, hist = collapse_count(PA, PB, rng)
        print(n, t, 'Korbits', k_orbits(PA, PB), 'extras0', hist[0], 'chords', c, 'hist', hist[:8])
