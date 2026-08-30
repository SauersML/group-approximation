# Problem LXXII: scattered primitive-spectrum collapse audit (2026-08-30)

## Result

Weak and plain pure infiniteness coincide for every C-star algebra whose
primitive ideal space is topologically scattered.  This is an intrinsic
topological sufficient condition and permits non-Hausdorff spectra,
uncountable Cantor--Bendixson height, and highly non-linearly ordered ideal
lattices.

## Self-contained topological construction

Starting from the empty open subset of `Prim(A)`, choose an isolated point
of the remaining subspace and add it.  Relative isolation makes the enlarged
set open in the full primitive space.  At limits take unions.  One new point
is added at every successor, so the process terminates after at most
`|Prim(A)|` steps.

Under the ideal/open-set correspondence, the resulting open filtration is a
continuous ideal filtration.  Each successor subquotient has one-point
primitive spectrum and is therefore simple.  The established transfinite
simple-layer theorem then runs pure-infinite extension permanence at
successors and inductive-limit permanence at limits.

No Hausdorff or `T_1` argument is hidden here.  The singleton successor
difference is locally closed, which is exactly what is needed for it to be
the primitive spectrum of an ideal subquotient.

## Boundary

The word "scattered" here is purely topological and refers to `Prim(A)`.
It is not the C-star property sometimes called scatteredness (being built
from elementary representations).  The simple successor layers may be
purely infinite; for example, ordinal direct sums of `O_infinity` fit the
theorem and can have large incomparable ideal families.
