"""Independent Todd--Coxeter (HLT with a completion pass) for <x, y | r1, r2>.

Second implementation for the balanced census.  For every line "<id> <L> <r1> <r2> ..."
it enumerates the cosets of the trivial subgroup with a coset limit and reports
"<id> <r1> <r2> ORDER <n>" when the table closes, "<id> <r1> <r2> OVERFLOW" at the limit, or
"<id> <r1> <r2> ERROR <msg>" if an internal consistency check fails.
Relator letters: x X y Y.  Coset 0 is the trivial subgroup.  Every coincidence processed is a
consequence of the relators (two definitions of the same coset times the same generator), so a
closed table gives an upper bound |G| <= n; the table is also re-checked as a consistent
transitive action in which every relator closes at every coset, which gives |G| >= n.
Usage: tc_verify.py IN OUT LIMIT
"""
import sys

GEN = {"x": 0, "X": 1, "y": 2, "Y": 3}
INVG = [1, 0, 3, 2]


class Table:
    def __init__(self, limit):
        self.limit = limit
        self.t = [[-1, -1, -1, -1]]
        self.p = [0]

    def find(self, c):
        root = c
        while self.p[root] != root:
            root = self.p[root]
        while self.p[c] != root:
            self.p[c], c = root, self.p[c]
        return root

    def new(self):
        if len(self.t) >= self.limit:
            raise OverflowError
        self.t.append([-1, -1, -1, -1])
        self.p.append(len(self.p))
        return len(self.t) - 1

    def get(self, c, g):
        d = self.t[c][g]
        return -1 if d == -1 else self.find(d)

    def define(self, c, g, d):
        self.t[c][g] = d
        self.t[d][INVG[g]] = c

    def coincidence(self, a, b):
        queue = [(a, b)]
        while queue:
            a, b = queue.pop()
            a, b = self.find(a), self.find(b)
            if a == b:
                continue
            if a > b:
                a, b = b, a
            self.p[b] = a
            for g in range(4):
                d = self.t[b][g]
                if d == -1:
                    continue
                self.t[b][g] = -1
                d = self.find(d)
                ea = self.get(a, g)
                if ea != -1:
                    queue.append((ea, d))
                else:
                    self.t[a][g] = d
                ed = self.get(d, INVG[g])
                if ed != -1 and ed != a:
                    queue.append((ed, a))
                else:
                    self.t[d][INVG[g]] = a

    def scan_and_fill(self, c, rel):
        n = len(rel)
        i, j = 0, n - 1
        f = b = self.find(c)
        while True:
            while i <= j and self.get(f, rel[i]) != -1:
                f = self.get(f, rel[i])
                i += 1
            if i > j:
                if f != self.find(c):
                    self.coincidence(f, c)
                return
            while j >= i and self.get(b, INVG[rel[j]]) != -1:
                b = self.get(b, INVG[rel[j]])
                j -= 1
            if j < i:
                self.coincidence(f, b)
                return
            if i == j:
                self.define(f, rel[i], b)
                return
            d = self.new()
            self.define(f, rel[i], d)

    def complete(self):
        # True iff every live coset has all entries defined and every relator closes everywhere
        for k in range(len(self.t)):
            if self.find(k) != k:
                continue
            for g in range(4):
                d = self.get(k, g)
                if d == -1 or self.get(d, INVG[g]) != k:
                    return False
        return True


def enumerate_trivial(rels, limit):
    T = Table(limit)
    for _ in range(1000):
        c = 0
        while c < len(T.t):
            if T.find(c) == c:
                for r in rels:
                    T.scan_and_fill(c, r)
                    if T.find(c) != c:
                        break
                if T.find(c) == c:
                    for g in range(4):
                        if T.get(c, g) == -1:
                            T.define(c, g, T.new())
            c += 1
        if T.complete():
            ok = True
            for k in range(len(T.t)):
                if T.find(k) != k:
                    continue
                for r in rels:
                    pt = k
                    for g in r:
                        pt = T.get(pt, g)
                    if pt != k:
                        ok = False
                        T.scan_and_fill(k, r)
            if ok:
                break
    else:
        raise AssertionError("no convergence")
    live = [k for k in range(len(T.t)) if T.find(k) == k]
    idx = {k: i for i, k in enumerate(live)}
    tab = [[idx[T.get(k, g)] for g in range(4)] for k in live]
    seen = {0}
    stack = [0]
    while stack:
        k = stack.pop()
        for g in range(4):
            if tab[k][g] not in seen:
                seen.add(tab[k][g])
                stack.append(tab[k][g])
    if len(seen) != len(tab):
        raise AssertionError("not transitive")
    for k in range(len(tab)):
        for g in range(4):
            if tab[tab[k][g]][INVG[g]] != k:
                raise AssertionError("inconsistent")
        for r in rels:
            pt = k
            for g in r:
                pt = tab[pt][g]
            if pt != k:
                raise AssertionError("relator open")
    return len(tab)


def main():
    inp, out, limit = sys.argv[1], sys.argv[2], int(sys.argv[3])
    with open(inp) as f, open(out, "w") as g:
        for ln in f:
            p = ln.split()
            if len(p) < 4:
                continue
            rels = [[GEN[ch] for ch in p[2]], [GEN[ch] for ch in p[3]]]
            try:
                n = enumerate_trivial(rels, limit)
                g.write("%s %s %s ORDER %d\n" % (p[0], p[2], p[3], n))
            except OverflowError:
                g.write("%s %s %s OVERFLOW\n" % (p[0], p[2], p[3]))
            except (AssertionError, KeyError, IndexError) as e:
                g.write("%s %s %s ERROR %s\n" % (p[0], p[2], p[3], str(e).replace(" ", "_")))
            g.flush()


if __name__ == "__main__":
    main()
