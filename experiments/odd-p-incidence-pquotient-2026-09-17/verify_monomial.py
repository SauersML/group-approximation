#!/usr/bin/env python3
"""Exact, GAP-independent check of a finite-dimensional operator solution.

Input: a JSON monomial representation {"N":N, "n":n, "chiJ":c, "gens":[{perm,phase},...]}
with one entry per edge variable x_e (in the edge order below) followed by J.
Each generator acts on the standard basis by  e_i -> zeta_N^{phase[i]} e_{perm[i]}
(row-vector / right-action convention, so words are applied left to right).
All arithmetic is exact (permutations and integers mod N).

Checks, for the oriented incidence system of the graph over Z_p with b = delta_{v0}:
  * J is the scalar zeta_N^{chiJ}, and zeta_N^{chiJ} is a primitive p-th root of unity;
  * X_e^p = I for every edge e;
  * X_e X_f = X_f X_e whenever e, f share a vertex;
  * for every vertex v: prod_{e at v} X_e^{sigma(v,e)} = J^{b_v}, sigma = +1 at head, -1 at tail;
  * sum_v b_v != 0 mod p, i.e. the system has no classical solution.
"""
import json
import sys


def heawood():
    E = [(i, (i + 1) % 14) for i in range(14)]
    E += [(i, (i + 5) % 14) for i in range(0, 14, 2)]
    return 14, E


def moebius_kantor():
    n = 16
    E = [(i, (i + 1) % n) for i in range(n)]
    for i in range(n):
        s = 5 if i % 2 == 0 else -5
        j = (i + s) % n
        if i < j:
            E.append((i, j))
    return n, E


def k1222():
    # K_{1,2,2,2}: apex 0, parts {1,2},{3,4},{5,6}; edges in lexicographic order (as in run_k1222_cert.g)
    part = [0, 1, 1, 2, 2, 3, 3]
    E = [(u, w) for u in range(7) for w in range(u + 1, 7) if part[u] != part[w]]
    return 7, E


GRAPHS = {"heawood": heawood, "moebius-kantor": moebius_kantor, "k1222": k1222}


class Mono:
    __slots__ = ("perm", "ph", "N")

    def __init__(self, perm, ph, N):
        self.perm, self.ph, self.N = list(perm), list(ph), N

    def __mul__(self, other):  # apply self, then other
        N = self.N
        perm = [other.perm[j] for j in self.perm]
        ph = [(self.ph[i] + other.ph[self.perm[i]]) % N for i in range(len(self.perm))]
        return Mono(perm, ph, N)

    def inv(self):
        n = len(self.perm)
        perm = [0] * n
        ph = [0] * n
        for i, j in enumerate(self.perm):
            perm[j] = i
            ph[j] = (-self.ph[i]) % self.N
        return Mono(perm, ph, self.N)

    def scalar(self):
        """Return c if this is zeta^c * I, else None."""
        if any(j != i for i, j in enumerate(self.perm)):
            return None
        c = self.ph[0]
        return c if all(x == c for x in self.ph) else None


def main(path, graph, p):
    data = json.load(open(path))
    N, n = data["N"], data["n"]
    nv, E = GRAPHS[graph]()
    gens = [Mono(g["perm"], g["phase"], N) for g in data["gens"]]
    assert len(gens) == len(E) + 1, "expected one generator per edge plus J"
    for g in gens:
        assert sorted(g.perm) == list(range(n)), "not a monomial unitary"
    X, J = gens[:-1], gens[-1]
    one = Mono(range(n), [0] * n, N)
    cJ = J.scalar()
    assert cJ is not None, "J is not scalar"
    assert (cJ * p) % N == 0 and cJ % N != 0, "J is not a primitive p-th root of unity"
    for e, x in enumerate(X):
        y = one
        for _ in range(p):
            y = y * x
        assert y.scalar() == 0, f"X_{e}^p != I"
    inc = {v: [e for e, (a, b) in enumerate(E) if v in (a, b)] for v in range(nv)}
    for v in range(nv):
        for e in inc[v]:
            for f in inc[v]:
                if e < f:
                    assert (X[e] * X[f]).perm == (X[f] * X[e]).perm and \
                        (X[e] * X[f]).ph == (X[f] * X[e]).ph, f"X_{e}, X_{f} do not commute"
    b = [1] + [0] * (nv - 1)
    for v in range(nv):
        w = one
        for e in inc[v]:
            head = E[e][1] == v
            w = w * (X[e] if head else X[e].inv())
        s = w.scalar()
        assert s is not None and s == (b[v] * cJ) % N, f"vertex relation fails at {v}"
    assert sum(b) % p != 0
    print(f"OK: {graph}, p={p}: exact operator solution in dimension {n}; "
          f"J = zeta_{N}^{cJ} (primitive {p}-th root of unity); sum b = {sum(b)} != 0 mod {p}, "
          f"so no classical solution exists.")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
