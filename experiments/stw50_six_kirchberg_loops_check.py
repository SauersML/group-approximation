#!/usr/bin/env python3
"""Exact integer certificates for the STW Problem L six-loop construction.

Companion to research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md and
to the Cairn region rooted at stw99-l-six-circle-actions-basis-of-pi1-aut.

Standard library only, exact integer arithmetic only -- no floats anywhere.
What is checked here is the FINITE part of the manuscript: graph incidences,
row supports and the two row relations at the level of formal words, the
lattice bases, the reduced invariant tables including the graded sign, and
the determinant / inverse / kernel-basis certificates.  What is NOT checked,
and cannot be by a script: Dadarlat's homotopy theorem, Kirchberg-Phillips,
the graph-algebra package, Kunneth, Pimsner-Voiculescu.  Those are imports,
each carried by its own -citation route in Cairn.

Run:  python3 experiments/stw50_six_kirchberg_loops_check.py
Exit: 0 iff every certificate holds.

NOTE: this file has NOT been executed in the nonsofic_existence checkout --
the standing order there is no local execution.  Run it on MSI or in CI.
"""

from fractions import Fraction
from itertools import product


# --------------------------------------------------------------------------
# 1.  The graph E(u): vertices 1..n, a distinguished loop d_i at each vertex,
#     and u_j edges a_{ij}^{(k)} : i -> j for every ordered pair (i,j).
# --------------------------------------------------------------------------

class Graph:
    def __init__(self, u):
        self.u = tuple(u)
        self.n = len(u)
        self.edges = []                      # (source, range, tag)
        for i in range(self.n):
            self.edges.append((i, i, ("d", i)))
            for j in range(self.n):
                for k in range(u[j]):
                    self.edges.append((i, j, ("a", i, j, k)))

    def adjacency(self):
        """M[i][j] = number of edges i -> j."""
        M = [[0] * self.n for _ in range(self.n)]
        for (s, r, _) in self.edges:
            M[s][r] += 1
        return M

    def out_edges(self, i):
        return [e for e in self.edges if e[0] == i]

    def row(self, i):
        """The row R_i of equation (3), as a list of (column, entry).

        Columns are the pairs (j, k) with 0 <= k <= u_j, ordered
        lexicographically.  An entry is ('s', edge) or ('p', vertex).
        """
        out = []
        for j in range(self.n):
            for k in range(self.u[j] + 1):
                if k < self.u[j]:
                    out.append(((j, k), ("s", (i, j, ("a", i, j, k)))))
                elif j == i:
                    out.append(((j, k), ("s", (i, i, ("d", i)))))
                else:
                    out.append(((j, k), ("p", j)))
        return out

    def n_columns(self):
        return sum(x + 1 for x in self.u)


def check_incidence(g, expected_M, name):
    """M(u)_{ij} = delta_{ij} + u_j, and I - M^t = -u 1^t."""
    M = g.adjacency()
    ok = M == expected_M
    formula = [[(1 if i == j else 0) + g.u[j] for j in range(g.n)]
               for i in range(g.n)]
    ok = ok and M == formula
    ImMt = [[(1 if i == j else 0) - M[j][i] for j in range(g.n)]
            for i in range(g.n)]
    rank_one = [[-g.u[i] for _ in range(g.n)] for i in range(g.n)]
    ok = ok and ImMt == rank_one
    report(f"[{name}] adjacency = delta + u_j and I - M^t = -u 1^t", ok)
    return ok


def check_row_relations(g, name):
    """R_i R_i^* = 1 and R_i^* R_i = P, verified on formal words.

    R_i R_i^* = sum_c entry_c entry_c^*.  Each edge entry contributes the
    range projection s_a s_a^*, each vertex entry contributes p_j.  The
    identity holds iff the multiset of contributions is
    {s_a s_a^* : s(a) = i} together with {p_j : j != i}, since the first
    group sums to p_i by the Cuntz-Krieger relation and adding the second
    gives sum_j p_j = 1.

    R_i^* R_i is diagonal with entry p_{r(a)} (edges) or p_j (vertices);
    the claim is that column (j,k) always yields p_j, for every i.
    """
    ok = True
    diagonals = []
    for i in range(g.n):
        r = g.row(i)
        ok = ok and len(r) == g.n_columns()

        edge_entries = [e for (_, (tag, e)) in
                        ((c, v) for (c, v) in r) if tag == "s"]
        # -- R_i R_i^* : the edge entries must be exactly the edges out of i
        ok = ok and sorted(edge_entries) == sorted(g.out_edges(i))
        vertex_entries = sorted(v for (_, (tag, v)) in r if tag == "p")
        ok = ok and vertex_entries == sorted(j for j in range(g.n) if j != i)

        # -- R_i^* R_i : diagonal entry of column (j,k)
        diag = {}
        for (col, val) in r:
            j, _k = col
            if val[0] == "s":
                diag[col] = val[1][1]            # range of the edge
            else:
                diag[col] = val[1]               # the vertex itself
            if diag[col] != j:
                ok = False
        diagonals.append(diag)

        # -- off-diagonal vanishing, entry by entry
        for (c1, v1), (c2, v2) in product(r, r):
            if c1 == c2:
                continue
            if v1[0] == "s" and v2[0] == "s":
                continue                         # distinct edges: s_a^* s_b = 0
            if v1[0] == "p" and v2[0] == "p":
                continue                         # distinct vertices: p_j p_k = 0
            # mixed: p_j s_a with j != s(a) = i, so p_j s_a = p_j p_i s_a = 0
            j = v1[1] if v1[0] == "p" else v2[1]
            if j == i:
                ok = False

    ok = ok and all(d == diagonals[0] for d in diagonals)
    report(f"[{name}] R_i R_i^* = 1, R_i^* R_i = P with P independent of i", ok)

    counts = {}
    for col, j in diagonals[0].items():
        counts[j] = counts.get(j, 0) + 1
    ok2 = counts == {j: g.u[j] + 1 for j in range(g.n)}
    report(f"[{name}] P carries u_j + 1 copies of p_j", ok2)
    return ok and ok2


# --------------------------------------------------------------------------
# 2.  Lattices.  K_0 = Z^n / Z u with u primitive-quotient basis checks,
#     K_1 = { x : sum x_i = 0 }.
# --------------------------------------------------------------------------

def det(M):
    """Exact determinant by fraction-free elimination."""
    A = [[Fraction(x) for x in row] for row in M]
    n = len(A)
    d = Fraction(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            d = -d
        d *= A[c][c]
        inv = Fraction(1) / A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] * inv
            if f:
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    assert d.denominator == 1
    return int(d)


def check_k0_basis_three_vertex():
    """K_0(C) = Z^3/Z(1,1,2) is free on e_C = (1,1,1) and b = (1,0,0),
    with [p_2] = 2 e_C - b and [p_3] = -e_C."""
    u = (1, 1, 2)
    e = (1, 1, 1)
    b = (1, 0, 0)
    cols = [[u[i], e[i], b[i]] for i in range(3)]
    ok = abs(det(cols)) == 1 and det(cols) == -1

    def reduce_mod_u(v):
        return tuple(v)

    p2 = tuple(2 * e[i] - b[i] for i in range(3))          # (1,2,2)
    ok = ok and tuple(p2[i] - (1 if i == 1 else 0) for i in range(3)) == u
    p3 = tuple(-e[i] for i in range(3))                     # (-1,-1,-1)
    ok = ok and tuple(p3[i] - (1 if i == 2 else 0) for i in range(3)) == \
        tuple(-x for x in u)
    report("[C] {e_C, b} is a Z-basis of K_0 (det = -1); "
           "[p_2] = 2e_C - b, [p_3] = -e_C", ok)
    return ok


def check_k0_basis_two_vertex():
    """K_0(B) = Z^2/Z(1,2) = Z via (x,y) -> 2x - y; [p]=2e_B, [q]=-e_B."""
    phi = lambda v: 2 * v[0] - v[1]
    ok = phi((1, 2)) == 0                       # kernel contains u
    ok = ok and phi((1, 1)) == 1                # e_B is a generator
    ok = ok and phi((1, 0)) == 2                # [p] = 2 e_B
    ok = ok and phi((0, 1)) == -1               # [q] = -e_B
    report("[B] K_0 = Z e_B with [p] = 2e_B, [q] = -e_B", ok)
    return ok


# --------------------------------------------------------------------------
# 3.  The invariant tables.  Delta_{g_{ij}}([W_k]) = delta_{ik} [p_j].
# --------------------------------------------------------------------------

def delta_edge_action(i, j, k, phase, vertex_class):
    """Value of Delta for the loop z -> g_{ij, z^phase} on the class [W_k],
    expressed in the K_0 basis via `vertex_class`."""
    if k != i:
        return (0, 0) if isinstance(vertex_class(j), tuple) else 0
    v = vertex_class(j)
    return tuple(phase * c for c in v) if isinstance(v, tuple) else phase * v


def check_three_vertex_table():
    """h_1 = g_{13,z^-1}, h_2 = g_{11,z}, h_3 = g_{23,z^-1}, h_4 = g_{21,z}
    give the four elementary matrix units of Hom(K_1(C), K_0(C))."""
    # K_0(C) coordinates are (coefficient of e_C, coefficient of b)
    vclass = {0: (0, 1), 1: (2, -1), 2: (-1, 0)}    # [p_1], [p_2], [p_3]
    loops = [("h_1", 0, 2, -1), ("h_2", 0, 0, +1),
             ("h_3", 1, 2, -1), ("h_4", 1, 0, +1)]
    want = {"h_1": [(1, 0), (0, 0)], "h_2": [(0, 1), (0, 0)],
            "h_3": [(0, 0), (1, 0)], "h_4": [(0, 0), (0, 1)]}
    ok = True
    for (nm, i, j, ph) in loops:
        got = [delta_edge_action(i, j, k, ph, lambda t: vclass[t])
               for k in (0, 1)]
        ok = ok and got == want[nm]
    report("[C] the h_j table is the four matrix units of Hom(K_1, K_0)", ok)
    return ok


def check_two_vertex_generator():
    """gamma = g_{12, z^-1} on B has Delta([V]) = -[q] = e_B, a unit,
    so [V] generates K_1(B)."""
    q_class = -1                                    # [q] = -e_B
    val = delta_edge_action(0, 1, 0, -1, lambda t: q_class)
    ok = val == 1
    report("[B] Delta_gamma([V]) = e_B is unimodular, so [V] generates K_1", ok)
    return ok


def check_tensor_signs():
    """The graded external product on K_*(B (x) B).

    Degrees: e_B is even, v is odd, and the suspension class t is odd.
    rho_1 replaces the FIRST factor's contribution, rho_2 the second; the
    sign is the Koszul sign of moving t to the front.
    """
    # basis of K_*(A) as pairs of B-classes, with degrees
    E, V = ("e", 0), ("v", 1)
    basis = {"e": (E, E), "beta": (V, V), "x": (V, E), "y": (E, V)}

    def apply(loop, name):
        """Delta_{rho_loop} on the named class; gamma sends v -> t (x) e_B
        and kills e_B."""
        f1, f2 = basis[name]
        if loop == 1:
            if f1 != V:
                return (0, None)
            out = ("e", 0) if True else None
            new = (E, f2)                # v replaced by e_B, t pulled out front
            sign = 1                     # t is already leftmost
        else:
            if f2 != V:
                return (0, None)
            new = (f1, E)
            sign = -1 if f1[1] % 2 else 1   # move odd t past f1
        for nm, pair in basis.items():
            if pair == new:
                return (sign, nm)
        return (0, None)

    got = {(l, nm): apply(l, nm) for l in (1, 2)
           for nm in ("x", "y", "beta", "e")}
    want = {(1, "x"): (1, "e"), (1, "y"): (0, None),
            (1, "beta"): (1, "y"), (1, "e"): (0, None),
            (2, "x"): (0, None), (2, "y"): (1, "e"),
            (2, "beta"): (-1, "x"), (2, "e"): (0, None)}
    ok = got == want
    report("[A] rho_1, rho_2 tables, including the Koszul sign "
           "Delta_{rho_2}(beta) = -x", ok)
    return ok


# --------------------------------------------------------------------------
# 4.  The certificate:  det L = 1, the inverse formula (16), the kernel basis.
# --------------------------------------------------------------------------

L = [[1, 0, 0, 0, 1, 0],
     [0, 1, 0, 0, 0, 0],
     [0, 0, 1, 0, 0, 1],
     [0, 0, 0, 1, 0, 0],
     [0, 0, 0, 0, 0, -1],
     [0, 0, 0, 0, 1, 0]]


def check_certificate():
    ok = det(L) == 1
    report("[L] det L = 1, so the six columns are a Z-basis of Z^6", ok)

    # equation (16): coefficients of (a,b,c,d,f,g) are (a-g, b, c+f, d, g, -f)
    ok2 = True
    for vec in [(1, 0, 0, 0, 0, 0), (0, 0, 0, 0, 1, 0), (0, 0, 0, 0, 0, 1),
                (3, -7, 5, 11, -2, 13)]:
        a, b, c, d, f, g = vec
        coeff = (a - g, b, c + f, d, g, -f)
        back = tuple(sum(L[r][k] * coeff[k] for k in range(6))
                     for r in range(6))
        ok2 = ok2 and back == vec
    report("[L] the inverse formula (a-g, b, c+f, d, g, -f) reproduces "
           "every class", ok2)

    # kappa columns: col2, col4, col5 - col1, col6 - col3
    col = lambda k: tuple(L[r][k] for r in range(6))
    sub = lambda p, q: tuple(a - b for a, b in zip(p, q))
    kappa = [col(1), col(3), sub(col(4), col(0)), sub(col(5), col(2))]
    ok3 = kappa == [(0, 1, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0),
                    (0, 0, 0, 0, 0, 1), (0, 0, 0, 0, -1, 0)]
    report("[kappa] the four kernel columns are equation (18)", ok3)

    # ker r = { a = c = 0 }: coordinates 0 and 2 vanish, and the remaining
    # 4x4 minor on coordinates 1,3,4,5 is unimodular.
    ok4 = all(k[0] == 0 and k[2] == 0 for k in kappa)
    minor = [[kappa[c][r] for c in range(4)] for r in (1, 3, 4, 5)]
    ok4 = ok4 and abs(det(minor)) == 1
    report("[kappa] they lie in ker r and span it (unimodular 4x4 minor)", ok4)
    return ok and ok2 and ok3 and ok4


# --------------------------------------------------------------------------

FAILURES = []


def report(msg, ok):
    print(("  ok   " if ok else "  FAIL ") + msg)
    if not ok:
        FAILURES.append(msg)


def main():
    print("STW Problem L -- six-loop construction, exact certificates")
    print()
    C = Graph((1, 1, 2))
    B = Graph((1, 2))

    print("graphs")
    check_incidence(C, [[2, 1, 2], [1, 2, 2], [1, 1, 3]], "C")
    check_incidence(B, [[2, 2], [1, 3]], "B")
    print("  ok   [C] 7 columns, [B] 5 columns"
          if (C.n_columns(), B.n_columns()) == (7, 5) else
          "  FAIL column counts")
    if (C.n_columns(), B.n_columns()) != (7, 5):
        FAILURES.append("column counts")

    print()
    print("rows")
    check_row_relations(C, "C")
    check_row_relations(B, "B")

    print()
    print("lattices")
    check_k0_basis_three_vertex()
    check_k0_basis_two_vertex()

    print()
    print("invariant tables")
    check_three_vertex_table()
    check_two_vertex_generator()
    check_tensor_signs()

    print()
    print("certificate")
    check_certificate()

    print()
    if FAILURES:
        print(f"FAILED ({len(FAILURES)}): " + "; ".join(FAILURES))
        return 1
    print("all certificates hold")
    print()
    print("NOT checked here (literature imports, each with its own Cairn")
    print("-citation route): Dadarlat's homotopy theorem, Kirchberg-Phillips,")
    print("Bates-Pask-Raeburn-Szymanski, Kumjian-Pask, Drinen-Tomforde,")
    print("Rosenberg-Schochet, Kunneth, Pimsner-Voiculescu.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
