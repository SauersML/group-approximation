---
rg: 2
id: finite-normalizer-star-no-go-proof
kind: route
title: Compute the marked Plancherel moment and extend it through every packet automorphism
target: finite-normalizer-star-no-go
requires:
  - central-marked-swap-star-has-two-word-trace-floor
---

The regular trace is the coefficient of the identity.  Expanding
`p=(1-y)/2` therefore gives `(FNA2)--(FNA3)`.  Its value is positive only
when `h=1`.  In that case the involutions `j_0,j_1` are equal.  Equality of
their off-diagonal swap blocks identifies the two partial isometries and
their ranges, so orthogonality makes the source zero.  This contradicts the
nonzero-star hypothesis.

For an automorphism `alpha`, the permutation unitary

```text
U_alpha delta_k=delta_(alpha(k))
```

satisfies `U_alpha lambda(g) U_alpha^*=lambda(alpha(g))`.  Hence the regular
packet extends through every automorphism actuator, proving `(FNA4)--(FNA5)`.
The finite-orbit statement is the identical calculation for a finite direct
power of `K` and its permutation group.
