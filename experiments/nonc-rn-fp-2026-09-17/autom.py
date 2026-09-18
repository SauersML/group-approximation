"""Automaton groups over X={0..d-1}: word-level sections, word problem, and K_infinity membership.

Convention: g = pi(g_0,...,g_{d-1}) acts by g(x w) = pi(x) g_x(w); products act on the left,
(gh)(v) = g(h(v)), so (gh)|_x = g|_{h(x)} h|_x.
A word is a tuple of nonzero ints: +i = generator i, -i = its inverse (generators 1..k).
"""
import sys
from functools import lru_cache

class Automaton:
    def __init__(self, d, gens):
        # gens: dict name -> (perm tuple, tuple of section names); names must be keys or 'e'
        self.d = d
        self.names = [n for n in gens]
        self.idx = {n: i + 1 for i, n in enumerate(self.names)}
        self.perm = {}
        self.sec = {}
        for n, (p, s) in gens.items():
            i = self.idx[n]
            self.perm[i] = tuple(p)
            self.sec[i] = tuple(() if t == 'e' else (self.idx[t],) for t in s)
            inv = [0] * d
            for x in range(d):
                inv[p[x]] = x
            self.perm[-i] = tuple(inv)
            # (g^-1)|_{x} = (g|_{g^-1(x)})^-1
            self.sec[-i] = tuple(tuple(-u for u in self.sec[i][inv[x]]) for x in range(d))

    def word(self, s):
        out = []
        for t in s.split():
            if t.endswith("'"):
                out.append(-self.idx[t[:-1]])
            else:
                out.append(self.idx[t])
        return tuple(out)

    @staticmethod
    def reduce(w):
        st = []
        for u in w:
            if st and st[-1] == -u:
                st.pop()
            else:
                st.append(u)
        return tuple(st)

    def act(self, w, x):
        """perm image of letter x and the word-level section w|_x (unreduced)."""
        secs = []
        for u in reversed(w):
            secs.append(self.sec[u][x])
            x = self.perm[u][x]
        # w = u_1 ... u_l, acting right to left; w|_x = u_1|_{..} ... u_l|_x
        res = []
        for s in reversed(secs):
            res.extend(s)
        return x, tuple(res)

    def sections(self, w):
        return [self.reduce(self.act(w, x)[1]) for x in range(self.d)]

    def root_perm(self, w):
        return tuple(self.act(w, x)[0] for x in range(self.d))

    def reach(self, w, cap=10**6):
        """All reduced words reachable from reduce(w) by iterated sections (finite: length non-increasing)."""
        w = self.reduce(w)
        seen = {w}
        stack = [w]
        while stack:
            u = stack.pop()
            for v in self.sections(u):
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
                    if len(seen) > cap:
                        raise RuntimeError('cap')
        return seen

    def is_trivial(self, w):
        ident = tuple(range(self.d))
        return all(self.root_perm(u) == ident for u in self.reach(w))

    def in_K_inf(self, w):
        """w in K_infinity iff trivial and the section graph on nonempty reachable words is acyclic."""
        R = self.reach(w)
        ident = tuple(range(self.d))
        if any(self.root_perm(u) != ident for u in R):
            return False
        # cycle detection among nonempty words
        color = {}
        sys.setrecursionlimit(100000)
        def dfs(u):
            color[u] = 1
            for v in self.sections(u):
                if not v:
                    continue
                c = color.get(v, 0)
                if c == 1:
                    return v
                if c == 0:
                    r = dfs(v)
                    if r is not None:
                        return r
            color[u] = 2
            return None
        for u in R:
            if u and color.get(u, 0) == 0:
                r = dfs(u)
                if r is not None:
                    return False
        return True

    def cycle_witness(self, w):
        """Return a nonempty reachable reduced word u and a path v with reduce(u|_v) = u, or None."""
        R = self.reach(w)
        for u in sorted(R, key=len):
            if not u:
                continue
            # BFS from u to see if u reachable from itself
            frontier = [(u, ())]
            seen = {u}
            while frontier:
                nf = []
                for z, path in frontier:
                    for x, v in enumerate(self.sections(z)):
                        if v == u:
                            return u, path + (x,)
                        if v and v not in seen:
                            seen.add(v)
                            nf.append((v, path + (x,)))
                frontier = nf
        return None

    def fmt(self, w):
        return ' '.join(self.names[abs(u) - 1] + ("'" if u < 0 else '') for u in w) or '1'
