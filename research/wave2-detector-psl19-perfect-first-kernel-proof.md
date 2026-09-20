---
rg: 2
id: wave2-detector-psl19-perfect-first-kernel-proof
kind: route
title: Enumerate the projective matrix triangle and compute its integral cellular boundary by unimodular elimination and two exact normal forms
target: wave2-detector-psl19-perfect-first-kernel
requires:
  - edge-twist-extensions-of-triangle-colimits-moment-test
artifacts:
  - research/artifacts/hyperbolic-rf-wave2-detectors-2026-09-20.md
  - experiments/hrf-wave2-detectors-2026-09-20/psl19_kernel.py
  - experiments/hrf-wave2-detectors-2026-09-20/psl19_kernel.out
---

The executable script enumerates all determinant-one matrices modulo 19
and identifies `M` with `-M` by lexicographically choosing one. It finds
3420 elements. For each stated matrix it enumerates its cyclic powers,
and breadth-first multiplication checks that every pair generates all
3420 elements. Link graphs have vertices the right cosets of the two
cyclic subgroups, with one edge for each element of `Q`. Their girths
are computed by breadth-first distances. One initial vertex suffices
because right multiplication by `Q` acts transitively on each vertex
type and every cycle meets both types. The returned girths are `(6,8,6)`.

Their half-girths are `(3,4,3)`, whose reciprocals sum to `11/12<1`.
The standard negatively curved triangle-of-groups development therefore
applies as in the prerequisite: the vertex groups embed and the group
acts properly and cocompactly on its CAT(-1) development. The kernel of
the canonical quotient acts freely, since the quotient is injective on
each simplex stabilizer. Hence the development is its contractible
universal cover.

In the quotient by `N`, every vertex type has one vertex, every edge
type has `3420/5=684` edges, and the faces are the 3420 elements of `Q`.
The boundary of the face `g` is its type-12 edge minus its type-13 edge
plus its type-23 edge. Collapsing the first edge of types12 and13 is a
spanning-tree collapse. Thus the cokernel of the remaining integer
`2050 by 3420` boundary matrix is `H_1(N;Z)`.

The script reduces this matrix as follows. A coefficient `v=±1` in row
`r`, column `c`, is used to subtract `a/v` times column `c` from any
other column having coefficient `a` in row `r`. This clears the row.
Then subtracting suitable multiples of row `r` from the other rows
would clear column `c`; those operations affect no other column. One
can consequently delete the unit row/column pair directly. These are
unimodular integer operations and preserve all nonunit Smith factors
and the free cokernel. Empty columns may also be deleted.

After 1962 such eliminations the matrix has 88 rows and 1458 columns.
The exact residual is stored. FLINT Smith normal form gives 88 unit
factors and no others. A second FLINT computation, Hermite normal form
of the transpose, yields `[I_88;0]`; the script checks every entry.
Thus the residual column lattice is all of `Z^88` and the original
cokernel is zero. This establishes `H_1(N;Z)=0` computationally.

The Euler characteristic is `3-2052+3420=1371`. The complex is connected
and two-dimensional; its second integral homology is free as a subgroup
of the free group of cellular 2-chains. Its rank is therefore 1370.

Trust scope: this is a complete exact integer computation with explicit
input and two normal-form checks using one external library (python-flint
0.9.0). It has not been replayed in a proof assistant. No empirical
statement about unenumerated finite quotients is used.
