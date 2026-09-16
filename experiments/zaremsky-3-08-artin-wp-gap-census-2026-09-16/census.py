#!/usr/bin/env python3
"""Rank-4 census for the word-problem gap of free-of-infinity Artin groups.

Scope: Coxeter matrices on 4 generators with every label in {2,...,MAXLAB}
(so free of infinity), up to relabelling of the generators.  For each
isomorphism class we record whether it is covered by one of the word-problem
results consulted on 2026-09-16:

  * reducible (Dynkin diagram disconnected): direct product of smaller
    Artin groups, each of rank <= 3, so covered (rank three, DPS Thm 7.4);
  * spherical (Gram matrix positive definite);
  * irreducible affine (Gram matrix positive semidefinite and singular);
  * no A3/B3 triple: no ordered triple (x,y,z) with m_xy = 3, m_xz = 2 and
    m_yz in {3,4} (Blasco-Garcia--Cumplido--Holt--Morris-Wright--Rees,
    arXiv:2412.12195, Theorem 1.1, diagram reading).  This contains large
    type and dimension <= 2, since an A3/B3 triple is spherical and has a 2;
  * cyclic type (Haettel--Huang, arXiv:2305.11622v2, Theorem E, source
    label thm:main1, with Theorem D for the word problem): Dynkin
    diagram a 4-cycle and every 3-subset spherical.

A class is UNCOVERED when none applies.  This is a finite illustration of the
gap, not a classification: labels above MAXLAB are not enumerated.

The theorem of arXiv:2412.12195 restates its hypothesis as "no subset {x,y,z}
... satisfies the relations xyx=yxy, xz=zx, (y,z)_n=(z,y)_n with n=3 or 4".
Read as relations holding in the group, this also excludes m_yz = 2, because
yz=zy implies (y,z)_4=(z,y)_4.  The script therefore also tallies the
conservative "literal" reading, in which m_yz ranges over {2,3,4}.

The Gram matrix is G_ii = 1, G_ij = -cos(pi/m_ij).  Eigenvalues are computed
in floating point; the script reports the smallest absolute eigenvalue among
eigenvalues it treats as nonzero, as a check on the tolerance.

A second part checks the five compact hyperbolic Coxeter 4-simplex diagrams
(rank 5, Lannér) directly.
"""
import itertools
import math
import sys

import numpy as np

MAXLAB = int(sys.argv[1]) if len(sys.argv) > 1 else 6
TOL = 1e-9
N = 4
EDGES = list(itertools.combinations(range(N), 2))

smallest_nonzero = [1.0]


def mat(lab, n=N):
    edges = list(itertools.combinations(range(n), 2))
    m = [[1] * n for _ in range(n)]
    for (i, j), v in zip(edges, lab):
        m[i][j] = m[j][i] = v
    return m


def canon(lab):
    m = mat(lab)
    best = None
    for p in itertools.permutations(range(N)):
        t = tuple(m[p[i]][p[j]] for i, j in EDGES)
        if best is None or t < best:
            best = t
    return best


def kind(m, idx):
    g = np.array([[1.0 if a == b else -math.cos(math.pi / m[a][b]) for b in idx] for a in idx])
    ev = np.linalg.eigvalsh(g)
    for e in ev:
        if abs(e) > TOL:
            smallest_nonzero[0] = min(smallest_nonzero[0], abs(e))
    if ev[0] > TOL:
        return "spherical"
    if ev[0] > -TOL:
        return "psd-singular"
    return "indefinite"


def connected(m):
    n = len(m)
    seen, stack = {0}, [0]
    while stack:
        a = stack.pop()
        for b in range(n):
            if b != a and m[a][b] >= 3 and b not in seen:
                seen.add(b)
                stack.append(b)
    return len(seen) == n


def a3b3_triples(m, literal=False):
    allowed = (2, 3, 4) if literal else (3, 4)
    return [
        (x, y, z)
        for x, y, z in itertools.permutations(range(len(m)), 3)
        if m[x][y] == 3 and m[x][z] == 2 and m[y][z] in allowed
    ]


def cyclic_type(m):
    n = len(m)
    deg = [sum(1 for b in range(n) if b != a and m[a][b] >= 3) for a in range(n)]
    if deg != [2] * n or not connected(m):
        return False
    return all(kind(m, list(T)) == "spherical" for T in itertools.combinations(range(n), n - 1))


def dynkin(m):
    n = len(m)
    return ",".join(f"{a}{b}:{m[a][b]}" for a, b in itertools.combinations(range(n), 2) if m[a][b] >= 3)


def tag(m, literal=False):
    if not connected(m):
        return "reducible"
    k = kind(m, list(range(len(m))))
    if k == "spherical":
        return "spherical"
    if k == "psd-singular":
        return "affine"
    if not a3b3_triples(m, literal):
        return "no-A3/B3"
    if cyclic_type(m):
        return "cyclic-type"
    return "UNCOVERED"


def lanner(m):
    n = len(m)
    return (
        connected(m)
        and kind(m, list(range(n))) == "indefinite"
        and all(kind(m, list(T)) == "spherical" for T in itertools.combinations(range(n), n - 1))
    )


TAGS = ["reducible", "spherical", "affine", "no-A3/B3", "cyclic-type", "UNCOVERED"]
classes = sorted({canon(lab) for lab in itertools.product(range(2, MAXLAB + 1), repeat=len(EDGES))})
tally = {"diagram": {}, "literal": {}}
uncovered = []
newly_uncovered_literal = []
for c in classes:
    m = mat(c)
    td, tl = tag(m), tag(m, literal=True)
    tally["diagram"][td] = tally["diagram"].get(td, 0) + 1
    tally["literal"][tl] = tally["literal"].get(tl, 0) + 1
    if td == "UNCOVERED":
        sph3 = sum(1 for T in itertools.combinations(range(N), 3) if kind(m, list(T)) == "spherical")
        uncovered.append((dynkin(m), sph3))
    elif tl == "UNCOVERED":
        newly_uncovered_literal.append(dynkin(m))

print(f"labels in 2..{MAXLAB}; isomorphism classes: {len(classes)}")
print("  tag          diagram-reading  literal-reading")
for t in TAGS:
    print(f"  {t:12s} {tally['diagram'].get(t, 0):8d} {tally['literal'].get(t, 0):16d}")

# Cross-checks against the classical lists (irreducible, labels <= MAXLAB).
sph = [dynkin(mat(c)) for c in classes if connected(mat(c)) and kind(mat(c), [0, 1, 2, 3]) == "spherical"]
aff = [dynkin(mat(c)) for c in classes if connected(mat(c)) and kind(mat(c), [0, 1, 2, 3]) == "psd-singular"]
lan = [mat(c) for c in classes if lanner(mat(c))]
cyc = [dynkin(mat(c)) for c in classes if cyclic_type(mat(c))]
print(f"irreducible spherical classes: {len(sph)} {sph}")
print(f"irreducible affine classes: {len(aff)} {aff}")
print(f"compact hyperbolic (all 3-subsets spherical, indefinite): {len(lan)}")
for mm in lan:
    print(f"    {dynkin(mm)}  -> diagram: {tag(mm)}; literal: {tag(mm, literal=True)}")
print(f"cyclic type classes: {len(cyc)} {cyc}")
print("uncovered classes, diagram reading (Dynkin edges with labels >= 3; number of spherical 3-subsets):")
for d, s in uncovered:
    print(f"    {d}   spherical triples: {s}")
print(f"covered under the diagram reading but UNCOVERED under the literal reading: {len(newly_uncovered_literal)}")
for d in newly_uncovered_literal:
    print(f"    {d}")


# Rank 5: the five compact hyperbolic Coxeter 4-simplex groups, checked directly.
def from_edges(n, edges):
    m = [[1 if a == b else 2 for b in range(n)] for a in range(n)]
    for a, b, v in edges:
        m[a][b] = m[b][a] = v
    return m


RANK5 = {
    "[5,3,3,3]": from_edges(5, [(0, 1, 5), (1, 2, 3), (2, 3, 3), (3, 4, 3)]),
    "[5,3,3,4]": from_edges(5, [(0, 1, 5), (1, 2, 3), (2, 3, 3), (3, 4, 4)]),
    "[5,3,3,5]": from_edges(5, [(0, 1, 5), (1, 2, 3), (2, 3, 3), (3, 4, 5)]),
    "[5,3,3^{1,1}]": from_edges(5, [(0, 1, 5), (1, 2, 3), (2, 3, 3), (2, 4, 3)]),
    "cycle 3-3-3-3-4": from_edges(5, [(0, 1, 3), (1, 2, 3), (2, 3, 3), (3, 4, 3), (4, 0, 4)]),
}
print("rank 5 compact hyperbolic diagrams:")
for name, mm in RANK5.items():
    print(f"    {name:16s} lanner={lanner(mm)}  diagram: {tag(mm)}; literal: {tag(mm, literal=True)}")
print(f"smallest nonzero |eigenvalue| seen: {smallest_nonzero[0]:.3e} (tolerance {TOL})")
