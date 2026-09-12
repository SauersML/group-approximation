---
rg: 2
id: balanced-overlay-sparse-sites-evade-hilbert-outlier-cut
kind: claim
title: Sparse full-rank site errors evade every fixed Hilbert-space outlier threshold
distinct_from:
  balanced-overlay-common-reducing-outlier-cut: that quarantines errors concentrated on a small Hilbert-space sector; this exhibits the transverse mode, errors concentrated on few logical coordinates but acting on the whole Hilbert space.
  sparse-clifford-cycles-refute-average-commutator-rounding: that corrupts every logical coordinate and stays a constant average distance from commuting tuples; this corrupts only two coordinates, is cheaply repairable in average HS, and diagnoses what the diffuse basin step must do.
  unbalanced-pair-sum-overlay-has-scalar-syndrome-escape: that is a constant-distance scalar countermodel to the unbalanced overlay; this survives balanced weighting only with vanishing coordinate distance and is not a countermodel to final rounding.
---

Let the balanced quadratic overlay have `L` logical coordinates, `M=Theta(L)`
bounded-width original checks, bounded column degree, `Theta(M)` copies of
each original check, and `Theta(M^2)` pair-sum/complete-pair faces.  On an
arbitrary even-dimensional Hilbert space choose anticommuting reflections
`A,B`, and set

```text
Q_1=A,  Q_2=B,  Q_i=I  (i>=3),                            (BSS1)
```

using identical values on every occurrence copy.

The balanced average squared relator energy is `O(1/L)`.  Equality and
involution defects vanish.  Only boundedly many original check types meet
coordinates `1` or `2`, so even after balanced repetition their bad faces
are `O(M)` among `Theta(M^2)`.  A pair-sum face can differ from the trivial
tuple only if at least one of its two original rows meets `{1,2}`; there are
again only `O(M)` such row pairs.  The same count includes every pair-sum
face in which `A` and `B` fail local commutation.  Finally only the logical
pair `{1,2}` fails the direct complete-pair commutator.  All word norms are
uniformly bounded, proving the energy estimate.

Every nonzero residual in this model acts at full matrix rank.  Since only
an `O(1/L)` fraction of the uniformly bounded positive residual squares is
nonzero, the raw balanced residual square function obeys the operator bound

```text
0 <= H_L <= (C/L) I.                                      (BSS2)
```

For every fixed threshold `a>0`, its high spectral projection is therefore
zero for all sufficiently large `L`.  A common Hilbert-space outlier cut
detects none of the error, even though `Q_1,Q_2` remain operator-norm far
from the trivial exact tuple.

This is not a counterexample to normalized-HS basin capture: replacing the
two corrupted logical coordinates by `I` costs only `O(1/L)` in the average
coordinate metric.  It proves that
`balanced-overlay-diffuse-square-function-newton` must include a sparse
**coordinate/site correction**.  Quarantining small Hilbert-space trace and
then applying a pointwise operator-norm Newton theorem cannot by itself
cover the balanced presentation.
