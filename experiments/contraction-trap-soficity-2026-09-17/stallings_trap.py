"""Stallings-folding checks for the rank-three contraction trap of EL_3(J).

The trap group is
    Gamma_3 = < a1,a2,a3,a4,c,d, g, e | g x g^-1 = phi(x) (x in F_6), [e, x] = 1 (x in F_6) >
with phi on the free group F_6 = F(a1,a2,a3,a4,c,d) given by relations (C1)-(C6):
    a1 -> a2
    a2 -> c U a1 U^-1
    a3 -> a4
    a4 -> U a3 U^-1 d^-1
    c  -> U c U^-1
    d  -> U d U^-1
    U  =  a2 a4^-1 a2 a1^-1 a3 a1^-1.

Checks (all exact, combinatorial):
  1. The Stallings core graph of H_1 = <phi(a1),...,phi(d)> has rank 6, so the six
     images are a free basis of H_1 and phi is injective (f.g. free groups are Hopfian).
  2. a1 is not in H_1 (membership by reading a1 in the folded graph).  By Britton's lemma
     this makes w = [e, g^-1 a1 g] nontrivial in Gamma_3.
  3. H_1 has infinite index in F_6 (the core graph is not a covering: some vertex lacks an
     outgoing edge for some letter).  So the nested chain H_j = phi^j(F_6) is strictly
     decreasing and the trap is a genuine proper contraction.
  4. Checks 1-2 for the rank-one sanity case phi(a) = a^2 (index 2 there, as expected).
Exit status 0 iff every check passes.
"""
import sys

GENS = ["a1", "a2", "a3", "a4", "c", "d"]


def inv(word):
    return [(x, -s) for (x, s) in reversed(word)]


def w(*letters):
    out = []
    for L in letters:
        if L.endswith("^-1"):
            out.append((L[:-3], -1))
        else:
            out.append((L, 1))
    return out


def reduce(word):
    out = []
    for x in word:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
            out.pop()
        else:
            out.append(x)
    return out


U = w("a2", "a4^-1", "a2", "a1^-1", "a3", "a1^-1")
PHI = {
    "a1": w("a2"),
    "a2": w("c") + U + w("a1") + inv(U),
    "a3": w("a4"),
    "a4": U + w("a3") + inv(U) + w("d^-1"),
    "c": U + w("c") + inv(U),
    "d": U + w("d") + inv(U),
}


class Graph:
    """Labelled graph; edges stored as out[v][(letter, sign)] = u (deterministic after folding)."""

    def __init__(self):
        self.n = 1  # base vertex 0
        self.edges = set()  # (v, letter, u) meaning v --letter--> u

    def new(self):
        self.n += 1
        return self.n - 1

    def add_loop(self, word):
        v = 0
        for i, (x, s) in enumerate(word):
            u = 0 if i == len(word) - 1 else self.new()
            if s == 1:
                self.edges.add((v, x, u))
            else:
                self.edges.add((u, x, v))
            v = u

    def fold(self):
        parent = list(range(self.n))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a

        changed = True
        while changed:
            changed = False
            edges = {(find(a), x, find(b)) for (a, x, b) in self.edges}
            out, inn = {}, {}
            for (a, x, b) in edges:
                k = (a, x)
                if k in out and out[k] != b:
                    parent[find(b)] = find(out[k])
                    changed = True
                    break
                out[k] = b
                k2 = (b, x)
                if k2 in inn and inn[k2] != a:
                    parent[find(a)] = find(inn[k2])
                    changed = True
                    break
                inn[k2] = a
            self.edges = edges
        self.edges = {(find(a), x, find(b)) for (a, x, b) in self.edges}
        self.verts = {find(v) for v in range(self.n)}
        self.base = find(0)

    def rank(self):
        return len(self.edges) - len(self.verts) + 1

    def reads(self, word):
        out = {(a, x): b for (a, x, b) in self.edges}
        inn = {(b, x): a for (a, x, b) in self.edges}
        v = self.base
        for (x, s) in word:
            nxt = out.get((v, x)) if s == 1 else inn.get((v, x))
            if nxt is None:
                return False
            v = nxt
        return v == self.base

    def is_covering(self, gens):
        out = {(a, x) for (a, x, b) in self.edges}
        inn = {(b, x) for (a, x, b) in self.edges}
        return all((v, x) in out and (v, x) in inn for v in self.verts for x in gens)


def check(name, images, gens, test_word, want_infinite_index=True):
    ok = True
    G = Graph()
    for x in gens:
        G.add_loop(reduce(images[x]))
    G.fold()
    r = G.rank()
    print(f"[{name}] core graph: {len(G.verts)} vertices, {len(G.edges)} edges, rank {r}")
    if r != len(gens):
        print(f"[{name}] FAIL: rank {r} != {len(gens)}, phi not shown injective")
        ok = False
    else:
        print(f"[{name}] PASS: images form a free basis, phi injective")
    for x in gens:
        if not G.reads(reduce(images[x])):
            print(f"[{name}] FAIL: image of {x} not read by core graph")
            ok = False
    mem = G.reads(test_word)
    print(f"[{name}] test word in phi(F)? {mem}")
    if mem:
        print(f"[{name}] FAIL: test word lies in phi(F)")
        ok = False
    else:
        print(f"[{name}] PASS: test word not in phi(F), so w = [e, g^-1 x g] != 1 by Britton")
    cov = G.is_covering(gens)
    print(f"[{name}] core graph is a covering (finite index)? {cov}")
    if cov and want_infinite_index:
        print(f"[{name}] FAIL: phi(F) has finite index")
        ok = False
    elif cov:
        print(f"[{name}] (finite index expected here; phi(F) != F since test word missing)")
    else:
        print(f"[{name}] PASS: phi(F) has infinite index, chain phi^j(F) strictly decreasing")
    return ok


def main():
    ok = True
    for x in GENS:
        print(x, "->", " ".join(f"{a}{'' if s == 1 else '^-1'}" for a, s in reduce(PHI[x])))
    ok &= check("EL3 trap", PHI, GENS, w("a1"))
    ok &= check("rank-one a->a^2", {"a": w("a", "a")}, ["a"], w("a"), want_infinite_index=False)
    print("ALL PASS" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
