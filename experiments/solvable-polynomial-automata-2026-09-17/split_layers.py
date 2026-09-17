#!/usr/bin/env python3
"""Polynomial splitting of abelian chief factors (solvable-polynomially-split-alphabets-two-way-kaplansky).

A finite group Q is *polynomially split along* an abelian minimal normal subgroup A if some unary polynomial
f in Pol_1(Q) = <constant maps, id> <= Q^Q (pointwise product) satisfies

    f(Q) <= A   and   f(a x) = a f(x)   for all a in A, x in Q.

Pol_1(Q) is the set of functions x -> w(x) with w a word with constants, so f is a word.

Method: H = Pol_1(Q) maps onto Hbar = {x -> f(x)A}; K = H cap A^Q is the kernel. Schreier generators
t(h) s t(h s)^-1 (s = constants and id) generate K; K is an F_p-subspace of A^Q = F_p^(d|Q|).
Splitting holds iff the affine condition f(ax) - f(x) = a is solvable inside span(K).
We also report whether K contains a function nonconstant on A (the T(1) != 0 condition).

Along every chief series 1 = Q_0 < ... < Q_r (explored over all choices of minimal normal abelian subgroups),
report for each layer p, d, q = |End_Q(A)|, e = d / log_p q, and whether Q/Q_(i-1) splits along Q_i/Q_(i-1).
"""
import itertools
import sys


# ---------- groups from permutation generators ----------
def compose(a, b):  # (a*b)(i) = a(b(i)) ; we use left-to-right product x*y := x o y
    return tuple(a[i] for i in b)


class Group:
    def __init__(self, name, gens=None, table=None):
        self.name = name
        if table is not None:
            self.n, self.T = len(table), table
        else:
            deg = len(gens[0])
            e = tuple(range(deg))
            elems, idx, frontier = [e], {e: 0}, [e]
            while frontier:
                new = []
                for x in frontier:
                    for g in gens:
                        y = compose(x, g)
                        if y not in idx:
                            idx[y] = len(elems)
                            elems.append(y)
                            new.append(y)
                frontier = new
            self.n = len(elems)
            self.T = [[idx[compose(x, y)] for y in elems] for x in elems]
        self.e = next(i for i in range(self.n) if all(self.T[i][j] == j for j in range(self.n)))
        self.inv = [next(j for j in range(self.n) if self.T[i][j] == self.e) for i in range(self.n)]

    def mul(self, x, y):
        return self.T[x][y]

    def closure(self, S):
        H = {self.e} | set(S)
        frontier = list(H)
        while frontier:
            new = []
            for x in frontier:
                for s in list(H):
                    for y in (self.T[x][s], self.T[s][x]):
                        if y not in H:
                            H.add(y)
                            new.append(y)
            frontier = new
        return frozenset(H)

    def normal_closure(self, S):
        H = set(S)
        while True:
            conj = {self.T[self.T[g][h]][self.inv[g]] for g in range(self.n) for h in H}
            H2 = self.closure(H | conj)
            if H2 == H:
                return frozenset(H2)
            H = set(H2)

    def minimal_normal(self):
        ncs = {self.normal_closure({x}) for x in range(self.n) if x != self.e}
        return [N for N in ncs if not any(M < N for M in ncs)]

    def order(self, x):
        k, y = 1, x
        while y != self.e:
            y, k = self.T[y][x], k + 1
        return k

    def quotient(self, N):
        cos, reps = {}, []
        for x in range(self.n):
            if x not in cos:
                c = len(reps)
                reps.append(x)
                for m in N:
                    cos[self.T[x][m]] = c
        table = [[cos[self.T[r][s]] for s in reps] for r in reps]
        return Group(self.name + "/N", table=table), cos


def elementary_abelian(G, A):
    A = sorted(A)
    if any(G.T[x][y] != G.T[y][x] for x in A for y in A):
        return None
    ords = {G.order(x) for x in A if x != G.e}
    if len(ords) != 1:
        return None
    p = ords.pop()
    if any(p % q == 0 for q in range(2, p)):
        return None
    # basis
    basis, span = [], {G.e: ()}
    coords = {G.e: ()}
    for x in A:
        if x in coords:
            continue
        basis.append(x)
        newc = {}
        for y, c in coords.items():
            z = y
            for k in range(p):
                newc[z] = c + (k,)
                z = G.T[z][x]
        coords = newc
    d = len(basis)
    coords = {x: tuple(c) + (0,) * (d - len(c)) for x, c in coords.items()}
    return p, d, coords


# ---------- F_p linear algebra ----------
class Echelon:
    def __init__(self, p, ncol):
        self.p, self.ncol, self.rows = p, ncol, {}  # pivot col -> row (normalized)

    def reduce(self, v):
        p = self.p
        v = list(v)
        for c, r in self.rows.items():
            if v[c]:
                f = v[c]
                v = [(a - f * b) % p for a, b in zip(v, r)]
        return v

    def add(self, v):
        v = self.reduce(v)
        c = next((i for i, a in enumerate(v) if a), None)
        if c is None:
            return False
        inv = pow(v[c], self.p - 2, self.p)
        v = [(a * inv) % self.p for a in v]
        for c2, r in list(self.rows.items()):
            if r[c]:
                f = r[c]
                self.rows[c2] = [(a - f * b) % self.p for a, b in zip(r, v)]
        self.rows[c] = v
        return True


def commutant_dim(G, A, p, d, coords):
    # matrices of conjugation by generators... use all elements
    basis = [x for x in A if coords[x].count(1) == 1 and sum(coords[x]) == 1]
    basis.sort(key=lambda x: coords[x].index(1))
    mats = []
    for g in range(G.n):
        cols = [coords[G.T[G.T[g][b]][G.inv[g]]] for b in basis]  # column j = image of basis j
        mats.append([[cols[j][i] for j in range(d)] for i in range(d)])
    # solve X M = M X, X in M_d(F_p): d^2 unknowns
    ech = Echelon(p, d * d)
    for M in mats:
        for i in range(d):
            for j in range(d):
                row = [0] * (d * d)
                for k in range(d):
                    row[i * d + k] = (row[i * d + k] + M[k][j]) % p   # (XM)_ij = sum_k X_ik M_kj
                    row[k * d + j] = (row[k * d + j] - M[i][k]) % p   # (MX)_ij = sum_k M_ik X_kj
                ech.add(row)
    return d * d - len(ech.rows)


def split_test(G, A, p, d, coords, cap=2_000_000):
    n = G.n
    Q, cos = G.quotient(A)
    one = tuple([G.e] * n)
    gens = [tuple([c] * n) for c in range(n)] + [tuple(range(n))]
    key = lambda f: tuple(cos[v] for v in f)
    trans = {key(one): one}
    order = [one]
    i = 0
    while i < len(order):
        f = order[i]
        i += 1
        for s in gens:
            g = tuple(G.T[a][b] for a, b in zip(f, s))
            k = key(g)
            if k not in trans:
                trans[k] = g
                order.append(g)
                if len(order) > cap:
                    return None
    ncol = d * n
    K = Echelon(p, ncol)
    full = ncol
    for f in order:
        for s in gens:
            g = tuple(G.T[a][b] for a, b in zip(f, s))
            t = trans[key(g)]
            k = tuple(G.T[a][G.inv[b]] for a, b in zip(g, t))
            vec = [c for v in k for c in coords[v]]
            K.add(vec)
            if len(K.rows) == full:
                break
    basis = list(K.rows.values())
    # T(1) != 0 : some basis function nonconstant on A
    Aset = sorted(A)
    nonconst = False
    for v in basis:
        vals = {tuple(v[d * a: d * a + d]) for a in Aset}
        if len(vals) > 1:
            nonconst = True
            break
    # splitting: unknown coefficients z (len(basis)); conditions f(ax)-f(x) = a for a in A, x in Q
    m = len(basis)
    ech = Echelon(p, m + 1)
    consistent = True
    for a in Aset:
        for x in range(n):
            ax = G.T[a][x]
            for j in range(d):
                row = [(basis[r][d * ax + j] - basis[r][d * x + j]) % p for r in range(m)] + [coords[a][j] % p]
                red = ech.reduce(row)
                if all(c == 0 for c in red[:m]) and red[m]:
                    consistent = False
                    break
                ech.add(row)
            if not consistent:
                break
        if not consistent:
            break
    verified = None
    if consistent:
        z = [0] * m
        for c, r in ech.rows.items():
            if c < m:
                z[c] = r[m]
        fv = [sum(z[r] * basis[r][i] for r in range(m)) % p for i in range(ncol)]
        verified = all(
            [(fv[d * G.T[a][x] + j] - fv[d * x + j]) % p for j in range(d)] == [coords[a][j] % p for j in range(d)]
            for a in Aset for x in range(n))
    return dict(pol_quot=len(order), dimK=m, nonconst=nonconst, split=consistent, verified=verified)


def is_solvable_residue_trivial(G):
    return G.n == 1


def chief_paths(G, depth=0, memo=None):
    """Yield lists of layer dicts along all chief series below Sol(G) (branching over minimal normal abelian A)."""
    if G.n == 1:
        yield []
        return
    mins = G.minimal_normal()
    ab = [(A, elementary_abelian(G, A)) for A in mins]
    ab = [(A, info) for A, info in ab if info is not None]
    if not ab:
        yield [dict(nonsolvable_residue=G.n)]
        return
    for A, (p, dd, coords) in ab:
        cd = commutant_dim(G, A, p, dd, coords)
        res = split_test(G, A, p, dd, coords)
        layer = dict(order=G.n, p=p, d=dd, q=p ** cd, e=dd // cd, **(res or dict(split=None)))
        Qt, _ = G.quotient(A)
        for rest in chief_paths(Qt, depth + 1):
            yield [layer] + rest


def perm(cycles, deg):
    a = list(range(deg))
    for cyc in cycles:
        for i in range(len(cyc)):
            a[cyc[i]] = cyc[(i + 1) % len(cyc)]
    return tuple(a)


def cyclic(n):
    return Group(f"Z/{n}", [perm([list(range(n))], n)])


def dihedral(n):
    return Group(f"D_{2*n}", [perm([list(range(n))], n), tuple((-i) % n for i in range(n))])


def direct(G, H, name):
    tab = [[G.T[a][c] * H.n + H.T[b][dd] for c in range(G.n) for dd in range(H.n)]
           for a in range(G.n) for b in range(H.n)]
    return Group(name, table=tab)


def affine(p, gen):  # F_p x| <gen> in F_p^*
    return Group(f"F_{p} x| <{gen}>", [perm([list(range(p))], p), tuple((gen * i) % p for i in range(p))])


def main():
    groups = [
        cyclic(4), direct(cyclic(2), cyclic(2), "Z/2^2"), cyclic(6), cyclic(8),
        dihedral(3), dihedral(4), dihedral(5), dihedral(6),
        Group("Q_8", table=None, gens=[perm([[0, 1, 4, 5], [2, 7, 6, 3]], 8), perm([[0, 2, 4, 6], [1, 3, 5, 7]], 8)]),
        Group("A_4", [perm([[0, 1, 2]], 4), perm([[0, 1], [2, 3]], 4)]),
        Group("S_4", [perm([[0, 1, 2, 3]], 4), perm([[0, 1]], 4)]),
        affine(5, 2), affine(7, 3), affine(7, 2),
        Group("Z/3 x| Z/4", [perm([[0, 1, 2]], 7), perm([[1, 2], [3, 4, 5, 6]], 7)]),
        direct(dihedral(3), cyclic(2), "S_3 x Z/2"),
        direct(dihedral(3), cyclic(3), "S_3 x Z/3"),
        Group("SL(2,3)", [perm([[0, 1, 4, 5], [2, 7, 6, 3]], 8), perm([[1, 2, 3], [5, 6, 7]], 8)]),
        Group("S_3 wr Z/2 (order 72)", [perm([[0, 1, 2]], 6), perm([[0, 1]], 6), perm([[0, 3], [1, 4], [2, 5]], 6)]),
        Group("A_5", [perm([[0, 1, 2, 3, 4]], 5), perm([[0, 1, 2]], 5)]),
        Group("S_5", [perm([[0, 1, 2, 3, 4]], 5), perm([[0, 1]], 5)]),
    ]
    for G in groups:
        paths = list(chief_paths(G))
        some_all_split = any(all(L.get("split") for L in path if "p" in L) and not any("nonsolvable_residue" in L for L in path)
                             for path in paths)
        print(f"== {G.name} (order {G.n}): {len(paths)} chief path(s); some path fully split: {some_all_split}")
        seen = set()
        for path in paths:
            s = " | ".join(
                (f"residue {L['nonsolvable_residue']}" if "nonsolvable_residue" in L else
                 f"|Q|={L['order']} F_{L['p']}^{L['d']} End=F_{L['q']} e={L['e']} split={L['split']} T1={L.get('nonconst')} certificate_checked={L.get('verified')}")
                for L in path)
            if s not in seen:
                seen.add(s)
                print("   ", s)
        sys.stdout.flush()


if __name__ == "__main__":
    main()
