---
rg: 2
id: wagon-wheel-hs-wall-proof
kind: route
title: Combine exact restriction with Slofstra's permutation-valued finite-coordinate construction
target: wagon-wheel-exact-radical-has-hs-wall
requires:
  - slofstra-solution-group-embedding-preserves-marked-involutions
  - slofstra-involution-not-sofic-radical
  - marked-approximate-radical-survives-solution-group-embedding
---

The source group in Slofstra's older separation has a central involution `J'`
which every exact finite-dimensional unitary representation kills. The exact
wagon-wheel embedding is injective and sends `J'` to the solution-group sign
`J`. Restricting an exact finite-dimensional representation of the output to
the embedded source therefore proves `pi(J)=I`.

On the other hand, `slofstra-involution-not-sofic-radical` constructs finite
permutation tuples for the same output presentation. Their relator Hamming
defects tend to zero, while the coordinate representative of `J` is the flip
on `X_n times {0,1}`. Thus it moves every point. For permutation matrices,

```text
||P-Q||_2^2=2 d_H(P,Q),
```

so the relator normalized-HS defects tend to zero and the sign remains at
distance `sqrt(2)`. Passing to a subsequence realizes any prescribed positive
error schedule tending to zero. This contradicts every proposed collapse
modulus `(WWH3)`.

Finally, the fixed-area word estimate in
`marked-approximate-radical-survives-solution-group-embedding` proves `(WWH4)`.
It explains why there is no contradiction: a bound on the output modulus is
obtained only from a bound on the source modulus near zero, not from exact
finite-dimensional vanishing at zero.
