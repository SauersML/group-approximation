---
rg: 2
id: rational-k1-detection-forces-infinite-order-unit-class
kind: claim
title: If K_1(R) detects the rational scalars up to a finitely generated kernel, then the unit class [1_R] has infinite order in K_0(R)
distinct_from:
  ibn-failure-makes-rational-scalars-elementary: that is the matrix statement for a given module isomorphism R^m ≅ R^(m+k); this is its K-theoretic contrapositive, stated for the (K1) half of the rational-scalar K-budget.
  rational-leavitt-path-k1-k2-scalar-dichotomy: that computes both halves for Leavitt path algebras of finite graphs through the ABC sequence; this is ring-general, one direction, and uses no K-theory computation of R.
  leavitt-scalar-commutators-block-fp-central-quotients: that treats rings with a Leavitt (1,d) family, where (d-1)[1] = 0; this covers every ring in which [1] has finite order, with or without a Leavitt family.
---

**ESTABLISHED** by `rational-k1-detection-forces-infinite-order-unit-class-proof`
(lane proof, not independently reviewed; elementary given the landed input; no novelty
claimed).

## Statement

Let `R` be a nonzero unital ring with a unital map `Q -> R`, and let
`ι: K_1(Q) = Q^x -> K_1(R)` be the induced map.
1. If `t [1_R] = 0` in `K_0(R)` for some `t >= 1`, then `ker ι ⊇ (Q^x)^(2st)` for some
   `s >= 1`, so `ker ι` is not finitely generated.
2. Equivalently: if `ker ι` is finitely generated, the (K1) half of the K-budget in
   `research/artifacts/gq-deep-adelic-1-k-budget.md`, then `[1_R]` has infinite order in
   `K_0(R)`. In particular `R^s ≇ R^(s+t)` for all `s, t >= 1`.

## Use

A host for `q-algebra-with-fp-simple-projective-elementary-group` must have `[1]` of
infinite order in `K_0`.
- For purely infinite simple rings this is the whole content of the Leavitt obstruction.
  It is also where the Leavitt path dichotomy
  (`rational-leavitt-path-k1-k2-scalar-dichotomy`) starts.
- The companion sufficient condition for the (K2) half is
  `matricial-divisibility-kills-rational-k2-symbols`. That condition wants `[1]` divisible
  by every integer, through ring isomorphisms `R ≅ M_n(R_n)`.
- Together they say the unit class must be of infinite order and infinitely divisible in
  the matricial sense, as in `U_Q = colim M_(n!)(Q)`.
