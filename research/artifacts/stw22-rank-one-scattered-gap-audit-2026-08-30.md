# STW XXII: Cantor--Bendixson rank-one fibre-gap audit

## Result

For the uniform tracial completion of `C(X) tensor U`, with `U` an
infinite-dimensional UHF algebra, every point having a clopen neighbourhood
whose puncture is discrete has fibre gap

```text
{2-norm-null families in product_D R}/{norm-null families}.
```

The cofinite-coordinate orthogonal-copy argument proves that this gap has no
nonzero bounded positive trace.  It may nevertheless be nonzero.

## Cantor--Bendixson consequence

If `X^(2)` is empty, the first derived set is compact and discrete, hence
finite.  Clopen localization reduces every nonisolated point to the computed
rank-one model; isolated points have zero gap.  The exact trace-free-gap
criterion therefore proves automatic uniform-`2`-norm continuity of every
trace on this completion.

For a scattered compact space of greater height, the same calculation shows
that any obstruction is supported on the second derived set.  This is a
strict localization statement, not an induction through arbitrary
Cantor--Bendixson rank.

## Why the induction stops

At a higher-rank point, a punctured neighbourhood contains its own limit
points.  Spectral supports can still be made fibrewise small, but the
unitaries producing arbitrarily many orthogonal copies must then vary
`2`-norm continuously over those lower-rank pieces.  The discrete-coordinate
proof supplies no such continuous selection.  Treating Cantor--Bendixson
rank as though it automatically supplied those conjugators would conceal the
same gluing problem as the general Bauer case.
