---
rg: 2
id: balanced-word-high-return-packing
kind: claim
title: Haar small-ball control bounds packings of balanced high-return unitary tuples
distinct_from:
  balanced-word-haar-small-ball: that controls Haar measure of a high-return locus; this converts that measure bound into an explicit metric packing bound using word Lipschitzness.
  unitary-word-return-entropy-summability: that asks for a summable weighted net over every dimension; this supplies the quantitative high-return layer estimate but does not yet prove the required exponent wins.
artifacts:
  - research/artifacts/random-relator-density-repair-2026-08-18.md
---

Let `mu` be supported on finitely many balanced nontrivial words of length at
most `L`, with the constants `alpha,rho` of
`balanced-word-haar-small-ball`.  Put

```text
p_(n,r)(U)=Pr_(w~mu)[d_2(w(U),1)<=r]
```

on `U(n)^k`, using the max normalized-HS metric on generator tuples.  Write
`v_n(s)` for Haar measure of a radius-`s` ball in `U(n)` and `beta_n(s)` for
Haar measure of a radius-`s` ball around `1` in `SU(n)`.

If `A` is an `eta`-separated subset of

```text
{U : p_(n,r)(U)>=q}
```

and `r+L eta/2 <= rho`, then

```text
|A| * v_n(eta/2)^k
 <= q^(-1) beta_n(r+L eta/2)^alpha.
```

Equivalently,

```text
|A| <= q^(-1) beta_n(r+L eta/2)^alpha / v_n(eta/2)^k.
```

This is the exact metric-entropy consequence of the available one-word
small-ball theorem.  It makes the residual difficulty measurable: a proof of
the random-relator route must either make this exponent beat the relevant
quotient-net entropy, or add genuinely multiword/structural information.
