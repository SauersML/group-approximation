# Existing Reynolds recovery does not align the two coefficient `C^4` algebras

Date: 2026-08-13

## Outcome

The coefficient anti-normalizer endpoint is valid, but the repository's
current property-`(T)` and finite-average theorems do not prove its alignment
hypothesis.  Treating them as if they did would reintroduce the same
coordinate-commutant gap identified in the eight-lamp spin reduction.

The terminal implication itself is quantitative.  If `F` is any raw
coefficient character cut and `G` any comb-transported character cut, then

```text
||F-G||_2^2=7/32>1/8.                                (RCA1)
```

Thus an alignment theorem only needs to put one matched pair below squared
distance `1/8`; convergence to zero is more than enough.  The strict endpoint
is kernel-checked as
`one_eighth_lt_hsDistSq_of_trace_flat_projections` in
`GroupApproximation/Sofic/DoublePauliCoefficient.lean`.

## What the existing machinery actually gives

`FiniteNormalAverageCorner.lean` constructs coordinate Reynolds averages for
a fixed finite normal subgroup, spectrally rounds their invariant corners,
and packages compressed microstates.  `InternalRadicalGap.lean` and the
Kazhdan-corner files perform the analogous operation for a prescribed
property-`(T)` subgroup.  These theorems recover a corner which is already
defined by approximate invariance under the selected subgroup.

The relative atlas implementer is in the opposite regime.  The exact estimate
in `TRUE_ATLAS_REYNOLDS_NORM_GATE.md` gives, along any hypothetical zero-defect
sequence,

```text
1-||E_H(U)||_2^2 >= c_0-o(1)                         (RCA2)
```

for an explicit `c_0>0`.  Hence `U` does not approach the finite-coordinate
commutant `rho(H)'`.  There is no commuting ultraproduct element to which a
commutant-lifting theorem can be directly applied.

The new coefficient algebra does not change this logical fact.  Its cuts are
fixed rational group-algebra polynomials, and the regular representation
realizes their full `7/32` anti-normalizer gap.  Therefore an abstract
von-Neumann-algebra argument cannot make the raw and transported `C^4`
algebras equal or nested.

## The missing simultaneous theorem

The sufficient matrix-specific statement is:

> **Comb-compatible coefficient alignment.**  In every finite-dimensional
> exact representation of the atlas source whose fixed quotient relators
> have normalized-HS defect `delta`, construct four raw and four transported
> multiplicity projections `P_epsilon,Q_eta`, within `o_delta(1)` of the
> marked group-algebra cuts, and a permutation `sigma` such that
> `max_eta ||P_(sigma eta)-Q_eta||_2^2 <= o_delta(1)`.

Together with convergence of the three marked moments to
`1/8,1/8,1/64`, any bound below `1/8` contradicts `(RCA1)`.

This theorem is stronger than:

- exactifying either finite coefficient packet separately;
- recovering the commutant of one already-commuting ultraproduct element;
- Reynolds averaging the relative implementer; or
- knowing the two abstract coefficient algebras are isomorphic.

It must recover the same finite multiplicity coordinates on both chart sides
and intertwine them with comb transport.  Equivalently, the spectral fallback
may recover only one trace-`1/120` well-conditioned block, but it must make
that block invariant under the multiplication arrows.

## Research consequence

The current work has not proved an explicit nonhyperlinear group.  It has
reduced this atlas candidate to a fixed eight-projection alignment theorem
with a strict `1/8` error budget and has shown why the existing formal library
does not supply that theorem.  Any final paper must either prove the
simultaneous statement above or take the independent perfect-completeness
route; citing generic Kazhdan/Reynolds recovery is insufficient.

