"""HLT Todd--Coxeter with coincidences, all generators involutions.

Enumerates cosets of H = C1,m = <w,u_0..u_m> in the presented group
Delta_(n,m) of overgroup_sat.py.  If the enumeration closes with one coset,
om lies in H in the presented group itself.
"""
import sys


def relators(n, m):
    W, O = 'w', 'o'
    u = [f'u{j}' for j in range(m + 1)]
    R = []
    nu = {}
    for j in range(n + 2, m + 1):
        nu[j] = [f'n{j}']
    for j in range(0, n):
        nu.setdefault(j, [W, u[j + 1], W])
    for j in range(1, n + 2):
        c = [O, u[j - 1], O]
        if j in nu:
            R.append(nu[j] + c[::-1])  # nu_j = c  <=>  nu_j c^-1 = 1
        else:
            nu[j] = c
    R.append([W, u[0]] * 3)
    for a in range(m + 1):
        for b in range(a + 1, m + 1):
            R.append([u[a], u[b]] * 2)
    R.append([O] + nu[0] + [O] + nu[0] + [O] + nu[0])
    for a in range(m + 1):
        for b in range(a + 1, m + 1):
            if (a < n and b < n) or (1 <= a <= n + 1 and 1 <= b <= n + 1):
                continue
            R.append((nu[a] + nu[b]) * 2)
    gens = [W, O] + u + [f'n{j}' for j in range(n + 2, m + 1)]
    H = [[W]] + [[x] for x in u]
    return gens, R, H


class TC:
    def __init__(self, gens):
        self.g = gens
        self.table = [dict()]
        self.p = [0]

    def rep(self, c):
        while self.p[c] != c:
            self.p[c] = self.p[self.p[c]]
            c = self.p[c]
        return c

    def new(self):
        self.table.append(dict())
        self.p.append(len(self.p))
        return len(self.p) - 1

    def coincide(self, a, b):
        q = [(a, b)]
        while q:
            a, b = q.pop()
            a, b = self.rep(a), self.rep(b)
            if a == b:
                continue
            if a > b:
                a, b = b, a
            self.p[b] = a
            for x, d in list(self.table[b].items()):
                d = self.rep(d)
                # remove inverse pointer d --x--> b (involution: same letter)
                if self.table[d].get(x) is not None and self.rep(self.table[d][x]) == b:
                    del self.table[d][x]
                ea = self.table[a].get(x)
                if ea is not None:
                    q.append((self.rep(ea), d))
                else:
                    self.table[a][x] = d
                    self.table[d][x] = a
            self.table[b] = dict()

    def define(self, c, x, d):
        self.table[c][x] = d
        self.table[d][x] = c

    def act(self, c, x):
        d = self.table[self.rep(c)].get(x)
        return None if d is None else self.rep(d)

    def scan_and_fill(self, c, word):
        c = self.rep(c)
        L = len(word)
        while True:
            f, i = c, 0
            while i < L and self.act(f, word[i]) is not None:
                f = self.act(f, word[i])
                i += 1
            if i == L:
                if f != c:
                    self.coincide(f, c)
                return
            b, j = c, L - 1
            while j >= i and self.act(b, word[j]) is not None:
                b = self.act(b, word[j])
                j -= 1
            if j < i:
                self.coincide(f, b)
                return
            if j == i:
                self.define(f, word[i], b)
                return
            d = self.new()
            self.define(f, word[i], d)

    def run(self, R, H, limit):
        for w_ in H:
            self.scan_and_fill(0, w_)
        c = 0
        while c < len(self.table):
            if len(self.table) > limit:
                return None
            if self.rep(c) == c:
                for r in R:
                    if self.rep(c) != c:
                        break
                    self.scan_and_fill(c, r)
                if self.rep(c) == c:
                    for x in self.g:
                        if self.rep(c) == c and self.act(c, x) is None:
                            d = self.new()
                            self.define(c, x, d)
            c += 1
        return len({self.rep(i) for i in range(len(self.table))})


if __name__ == '__main__':
    n, m, limit = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    gens, R, H = relators(n, m)
    T = TC(gens)
    idx = T.run(R, H, limit)
    print(f'n={n} m={m}: index of C1,m =', idx if idx is not None else f'> limit {limit} (not closed)')
