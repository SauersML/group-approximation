---
rg: 2
id: bounded-neighbor-pauli-constant-model-proof
kind: route
title: Strong-color a sparse signed graph and reuse finitely many Pauli coordinates
target: bounded-neighbor-pauli-needs-growing-equality-components
requires: []
---

Color the square of `G`.  Its maximum degree is at most `Delta^2`, so there
is a coloring

```text
kappa:V -> {1,...,C},       C=Delta^2+1,                         (1)
```

in which vertices at distance at most two have different colors.  Allocate
one qubit `Q_{a,b}` for every unordered pair of distinct colors `{a,b}`.

For a vertex `v` of color `a`, define a Pauli word `U_v` as follows.  For
each neighbor `w` of color `b`, use only the coordinate `Q_{a,b}` belonging
to that edge.  On an edge in `E_0`, put `X` at both endpoints.  On an edge in
`E_1`, put `X` at the endpoint with smaller color and `Z` at the endpoint
with larger color.  Put the identity on all remaining coordinates and take
the tensor product.

The distance-two coloring has two consequences.  First, a vertex has at
most one neighbor of any given color, so the prescription of `U_v` is
unambiguous.  Second, if `uv` is an edge with colors `a,b`, the supports of
`U_u` and `U_v` intersect in exactly the one coordinate `Q_{a,b}`: an
additional common coordinate would give edges from `u` and `v` with the
same unordered endpoint-color pair, which forces the current edge again.
Hence

```text
U_u U_v = (-1)^b U_v U_u       for uv in E_b.                   (2)
```

Every `U_v` is a selfadjoint unitary and the ambient dimension is `2^m`,
where `m=binom(C,2)`.  Isolated vertices may be assigned the identity (or a
commuting extra Pauli coordinate if nonidentity is desired).

For the equality extension, contract every equality component.  A component
of size at most `M` is incident to at most `M Delta` signed edges, so the
contracted signed graph has maximum degree at most `M Delta` after redundant
parallel constraints are removed.  Contradictory parallel signs would make
the original exact test inconsistent; otherwise apply the construction
above to the contracted graph and assign its one observable to every member
of the corresponding equality component.  This satisfies all tests exactly
in a dimension depending only on `M,Delta`.
