---
rg: 2
id: km-opposition-class-walk-threshold-proof
kind: route
title: Torsor transitivity, the alpha-string module, and Vandermonde on the rational normal curve
target: km-opposition-class-walk-threshold-law
requires: []
---

**Step 1 (torsor).**  The radical `U` of the panel-line's parabolic
fixes the line pointwise, hence preserves classes, and acts simply
transitively on the opposite lines (the opposite big cell of the
`BN`-pair); it acts transitively on each class with point stabilizers
`S_c` of order `q` (orbit counts `q^5` lines, `q^4` points per class
for the hexagon; `q^3`, `q^2` for the quadrangle; verified in the
computations).

**Step 2 (walks are stabilizer translations).**  A one-step move
between opposite lines sharing a class-`c` point is effected by an
element fixing that point, so the reachability group of `G_S` from the
base line is the subgroup `<S_c : c in S>` of `U`, and the components
are its orbits: their number is the index `[U : <S_c : c in S>]`.

**Step 3 (the curve).**  The Levi `SL_2` acts on `U/Phi(U)` as the
`alpha`-string module through the panel root: a string of length `d`
(four for the hexagon line radical `beta, beta+alpha, beta+2alpha,
beta+3alpha`; three for the abelian Siegel radical of the quadrangle;
two for point-panels).  The stabilizer of the apartment class is the
string-end root subgroup, and conjugating by the Levi elements
parametrizing the other classes gives Frattini images
`(1, lambda, lambda^2, ..., lambda^(d-1))` -- the rational normal
curve of degree `d-1`, with integral divided-power coefficients, in
every characteristic.

**Step 4 (Vandermonde).**  Any `min(|S|, d)` distinct curve points are
linearly independent (Vandermonde determinant, nonzero for distinct
parameters over any field), so the images of `{S_c : c in S}` span a
subspace of dimension `min(|S|, d)` of `U/Phi(U)`; by the Frattini
property `<S_c : c in S>` is the preimage of that span, of index
`q^(d - min(|S|,d))` in `U`.  This gives the component count, and
`|S| >= d` gives generation of `U`, hence connectivity.

**Step 5 (verification).**  The computed component patterns at
`q = 2, 3, 4, 5` (hexagon, all deletion depths) and `q = 3`
(quadrangle) match `q^(max(0,d-|S|))` in every case, including both
even and odd characteristic and characteristic three; the earlier
characteristic-two collapse claim, which contradicted this law at even
`q >= 4`, was traced to using an adjoint structure constant in place
of a seven-dimensional-module matrix element and is retracted.
