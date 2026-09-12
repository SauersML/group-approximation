---
rg: 2
id: canonical-swap-corner-dilation-budget-proof
kind: route
title: Combine the canonical arcsine law with the exact singular-value padding cost
target: canonical-swap-corners-have-no-dimension-descent
requires:
  - canonical-arithmetic-swap-fold-gram-is-arcsine
artifacts:
  - research/artifacts/sl3-corner-descent-dilation-budget-2026-09-05.md
---

For an `r x r` contraction `A` with singular values
`a_1 >= ... >= a_r`, the squared distance in normalized HS norm to a
compression of a unitary of size `r+k`, for `0<=k<=r`, is exactly

```text
(1/r) sum_(i=1)^(r-k) (1-a_i)^2.                         (CDP1)
```

The lower bound follows because such a compression has at least `r-k`
singular values equal to one. The singular-value squared-distance bound
then applies. Equality follows by setting the largest `r-k` singular
values of `A` to one and dilating each remaining singular value in one
two-dimensional rotation block. The artifact proves both assertions.

The nonzero corner spectral measure of `A_n^* A_n` is the same as that of
`Q_n P_n Q_n` in the normalized `Q_n` corner, where
`Q_n=H_n P_n H_n^*`. The required canonical law therefore gives singular
value distribution with density `2/(pi sqrt(1-a^2))` on `[0,1]`.
Its continuity makes the trimmed sum `(CDP1)` converge to the integral
over the largest `1-beta` fraction. Substituting `a=cos(theta)` evaluates
that integral as `(CDB1)`. It is positive for every `beta<1`, so an
`o(1)`-error sequence must satisfy `(CDB2)`.

The claim is restricted to preserving the compressed actor. No extension
of the compressed lattice representation to the full arithmetic group is
assumed or inferred.
