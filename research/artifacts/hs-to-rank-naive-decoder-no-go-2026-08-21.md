# Why the elementary HS-to-rank decoders fail

The desired bridge from a hyperlinear microstate to a linear-sofic model must
turn small normalized Hilbert--Schmidt multiplication defects into small
normalized-rank defects.  The two metrics have no one-sided comparison.

Choose `epsilon/(2 pi)` irrational and arbitrarily small.  For
`U_epsilon=exp(i epsilon)I_d`,

```text
||U_epsilon-I||_2=|exp(i epsilon)-1|,
rank(U_epsilon-I)/d=1.
```

This example is already central and dimension one in substance, so a random
basis cannot spread it more favourably.  Direct sums preserve the normalized
rank.  Every positive tensor power remains scalar and full-rank by the
irrational choice.  The defect has zero kernel and full image, so exact
kernel restriction or image quotient deletes the entire carrier.

Singular-value thresholding can replace this one `U_epsilon` by `I`, but the
replacement cannot be made into a multiplicative scalar rule.  A
multiplicative rule on the circle that kills a neighbourhood of one kills the
whole circle: take a sufficiently large root of any prescribed phase inside
that neighbourhood.  Relation-by-relation clipping therefore creates a
coherence problem rather than a rank approximation.

This does not rule out a decoder that uses the full finite multiplication
table to choose a global algebraic congruence.  It identifies what such a
decoder must add: correlated, table-level repair.  The spherical
defect-congruence lane attempts that repair after passing to matchings; the
Steinberg root-kernel lane attempts it through character orbits.  Neither is
obtained by amplification or thresholding alone.
