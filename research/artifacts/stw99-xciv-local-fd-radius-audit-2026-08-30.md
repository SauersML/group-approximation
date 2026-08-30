# STW Problem XCIV: local finite-dimensional radius audit

## Quantitative local invariant

For a finite tuple `F subset R`, define `alpha_R(F)` as its best common
operator-norm distance to a unital finite-dimensional subalgebra.  Define
`gamma_D(F)` as the smallest commutator defect of a unital copy of the fixed
block `D=I_(2,3)` against `F` on fixed contractive generators.

Every finite-dimensional unital `E subset R` has relative commutant a finite
direct sum of II1 factors.  Each summand contains a unital `D`, and the direct
sum gives one unital `D->E' intersect R`.  If `F` lies within `eta` of `E`,
this copy has commutator defect at most `2 eta`.  Hence

```text
gamma_D(F)<=2 alpha_R(F).
```

No coherent tower and no Bratteli multiplicity are needed for this local
estimate.  Those hypotheses were needed by the earlier theorem to keep an
entire generated hull Z-stable through infinitely many stages.

## Positive finite-test classes

A finite type-I von Neumann algebra of uniformly bounded degree is uniformly
locally finite-dimensional in operator norm: approximate finitely many
matrix-valued measurable functions by common finite-range simple functions.
Therefore every finite tuple in such an algebra has zero fixed-block defect.
In particular, every commuting normal finite tuple in `R` admits arbitrarily
norm-central copies of `I_(2,3)`, even if its joint von Neumann algebra is a
MASA and has no exact noncommutative relative commutant.

This last point is genuinely different from the exact commuting-CAR route.
The block commutes with a nearby finite spectral partition, not with the
original MASA.

## Boundary of the result

The result is local.  After adjoining one block, later finite tests need not
remain in the original type-I algebra, so this estimate alone does not build
a Z-stable hull for an arbitrary separable type-I seed.

A negative XCIV certificate with defect `delta` must have finite-dimensional
norm radius at least `delta/2`.  Hyperfiniteness only makes the analogous
`2`-norm radius zero.  The Pauli-corner obstruction shows why the two radii
cannot be identified by representative selection.
