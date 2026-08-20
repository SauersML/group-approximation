---
rg: 2
id: two-generator-amitsur-levitzki-dimension-oracle-proof
kind: route
title: Parse xx-separated monomials and apply the standard identity in size d
target: two-generator-amitsur-levitzki-dimension-oracle
requires: []
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
---

For a permutation `(j_1,...,j_(2n))` of `(1,...,2n)`, the corresponding
summand of `p_n` is

```text
x y^(j_1) x x y^(j_2) x ... x y^(j_(2n)) x.
```

Every exponent is positive, so the `xx` separators recover the ordered list
of exponents.  Distinct permutations therefore give distinct free monomials;
their coefficients are `+1` or `-1`, and no cancellation is possible.  This
proves `(ALO1)`.

For `rho:C<x,y> -> M_d(C)`, substitute the matrices
`rho(u_1),...,rho(u_(2d))` into the Amitsur--Levitzki standard identity of
degree `2d`; this is precisely `rho(p_d)=0`, proving `(ALO2)`.

The free algebra embeds in its free skew field and each nonzero `p_n` is
invertible there.  The universal algebra with formal two-sided inverses for all
`p_n` maps into that skew field and is therefore nonzero.  A unital
`d`-dimensional representation would send the `d`th inverse relation to
`0 q_d=1`, impossible.

