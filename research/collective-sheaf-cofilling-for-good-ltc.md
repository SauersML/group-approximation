---
rg: 2
id: collective-sheaf-cofilling-for-good-ltc
kind: claim
title: Upgrade a good degree-zero sheaf LTC from ordinary to collective cofilling
distinct_from:
  collective-cofilling-is-common-erasure-cleaning: that proves the exact equivalence and gives constant-coefficient examples; this asks for the same property on a good sheaf code.
  constant-cochain-collective-codes-lose-distance: that shows why positive-degree constant coefficients fail; degree-zero nonconstant sheaves avoid bounded coboundaries.
---

First--Kaufman, arXiv:2403.19388, construct good 2-query LTCs as degree-zero
cocycle codes of nonconstant binary sheaves: constant rate, linear distance,
and ordinary cosystolic/LTC soundness.  Because degree zero has no forced
bounded-weight coboundaries, these codes evade
`constant-cochain-collective-codes-lose-distance`.

The exact desired upgrade is the simultaneous-support estimate

```text
for every family beta_t in im(d_0),
choose d_0 a_t=beta_t with
|union_t supp(a_t)| <= K |union_t supp(beta_t)|.          (SCC1)
```

For the double-Cayley sheaves used in their construction, every hypothesis
of their degree-zero local-to-global criterion amplifies formally except
one: agreement testability of the fixed inner tensor code.  More precisely,
`inner-tensor-agreement-is-amplification-stable` implies `(SCC1)` by applying
First--Kaufman Theorem 8.10 to finite direct sums of the sheaf, with constants
independent of the number of summands.

Proving the amplified inner agreement claim would immediately
give a bounded-degree, positive-rate, linear-distance instance of common
erasure cleaning by `collective-cofilling-is-common-erasure-cleaning` and
would close the projective far-valley sector.  Equivalently, one may prove
that their local correction algorithm admits an erased-set-dependent
support envelope of size `O(|E|)` independent of the input syndrome.

Primary source: https://arxiv.org/abs/2403.19388

## Attempts

* **Run the published correction algorithm on every erased syndrome.**  The
  algorithm gives `O(|E|)` correction weight separately for each input, but
  its sequence of chosen local corrections depends on that input.  Taking
  the union over `dim(im(d_0) cap F_2^E)` independent syndromes can therefore
  cost exponentially more than `|E|`; no common support envelope is proved.
* **Reuse the constant-sheaf collective theorem.**  Kaufman--Tessler's
  collective argument is proved for the constant-coefficient simplicial
  complex.  First--Kaufman's restriction maps and varying stalks are used
  essentially to obtain positive rate.  An extension of the collective
  local-minimality argument to these sheaves is not stated, and ordinary
  cosystolic expansion alone does not imply the simultaneous estimate.
* **Amplify the published inner-code hypothesis.**  The local distance
  hypotheses preserve their constants under direct sums, but the local
  `cbe_0` hypothesis is agreement testability of `C_A tensor C_B`.  Its
  direct-sum form is exactly the new common-support lemma recorded in
  `inner-tensor-agreement-is-amplification-stable`; ordinary agreement
  testability is only its one-summand case.
