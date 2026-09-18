"""Induction step of the generator-rigidity theorem (artifact §4), as a finite local check.

For d >= 3, Delta_{d+1} is the dumbbell with base loop a, bridge beta_{d+1} = beta_d lambda_d
and loop lambda_{d+1} = beta_d^{-1} a beta_d lambda_d^{-1}; beta_d begins with
BETA3 = beta_3 = baBBabbA.  Near the base and near the a-edge y -> z of the loop, the graph is
    base o: a-loop, bridge reading BETA3 from o;
    loop segment reading BETA3^{-1} a BETA3, with y, z the ends of its middle a-edge.
All interior vertices of these paths have degree 2 in Delta_{d+1}.  The path ends are boundary
vertices: their remaining half-edges are not modelled.

The candidate pairs are {p, q} with p in pi^{-1}(0) = {o, y, z} and q in pi^{-1}(0b) or
pi^{-1}(0ba), except the two targets (o, ob), (o, oba).  For each, we run the folding closure
of model/(p ~ q).  If no boundary vertex ever joins a nontrivial class, the closure equals the
global folding restricted to the merged classes, so the global result keeps all but a few
vertices of Delta_{d+1} (>= 49) and is not the rose.
"""
from fg import INV

BETA3 = "baBBabbA"


class Model:
    def __init__(self):
        self.n = 0
        self.adj = {}  # (v, letter) -> v
        self.boundary = set()

    def new(self):
        self.n += 1
        return self.n - 1

    def edge(self, u, x, v):
        assert (u, x) not in self.adj and (v, INV[x]) not in self.adj
        self.adj[(u, x)] = v
        self.adj[(v, INV[x])] = u

    def path(self, u, word):
        verts = [u]
        for x in word:
            v = self.new()
            self.edge(verts[-1], x, v)
            verts.append(v)
        return verts


def build():
    M = Model()
    o = M.new()
    M.edge(o, "a", o)
    bridge = M.path(o, BETA3)
    M.boundary.add(bridge[-1])
    # loop segment: start -BETA3^{-1}-> y -a-> z -BETA3-> end, built from y outward
    y = M.new()
    back = M.path(y, BETA3)          # y -BETA3-> start, i.e. start -BETA3^{-1}-> y
    z = M.new()
    M.edge(y, "a", z)
    fwd = M.path(z, BETA3)
    M.boundary.add(back[-1])
    M.boundary.add(fwd[-1])
    names = {"o": o, "y": y, "z": z,
             "ob": bridge[1], "oba": bridge[2],
             "yb": back[1], "yba": back[2],
             "zb": fwd[1], "zba": fwd[2]}
    return M, names


def closure(M, p, q):
    parent = list(range(M.n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    parent[find(q)] = find(p)
    changed = True
    while changed:
        changed = False
        table = {}
        for (u, x), v in M.adj.items():
            key = (find(u), x)
            if key in table and find(table[key]) != find(v):
                parent[find(v)] = find(table[key])
                changed = True
            else:
                table.setdefault(key, v)
    classes = {}
    for v in range(M.n):
        classes.setdefault(find(v), []).append(v)
    big = [c for c in classes.values() if len(c) > 1]
    touched = any(v in M.boundary for c in big for v in c)
    merges = sum(len(c) - 1 for c in big)
    return touched, merges, big


def main():
    M, N = build()
    labels = {v: sorted(x for (u, x) in M.adj if u == v) for v in N.values()}
    for k, v in N.items():
        print(f"  labels at {k}: {labels[v]}")
    targets = {("o", "ob"), ("o", "oba")}
    ok = True
    for p in ("o", "y", "z"):
        for q in ("ob", "yb", "zb", "oba", "yba", "zba"):
            if (p, q) in targets:
                continue
            touched, merges, big = closure(M, N[p], N[q])
            status = "boundary touched" if touched else "local"
            print(f"pair ({p},{q}): {status}, vertex merges={merges}, classes={len(big)}")
            ok &= not touched
    print("ALL NON-TARGET CANDIDATES CLOSE LOCALLY" if ok else "CHECK FAILED")
    for p, q in sorted(targets):
        touched, merges, big = closure(M, N[p], N[q])
        print(f"target ({p},{q}): boundary touched={touched} (expected: the fold propagates)")


if __name__ == "__main__":
    main()
