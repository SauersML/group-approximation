---
rg: 2
id: pauli-sums-near-their-one-norm-round-to-stabilizer-states
kind: claim
title: A Pauli sum within F of its 1-norm has a stabilizer state within (1+sqrt2)F of its top eigenvalue
artifacts:
  - research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md
distinct_from:
  product-states-approximate-high-degree-2-local: that rounds to product states using high degree of a 2-local constraint graph; this rounds to stabilizer states using only the gap between the Pauli 1-norm and the top eigenvalue, with terms of any weight and no degree or locality assumption.
  commuting-hamiltonians-on-small-set-expanders-in-np: that needs commuting terms on almost perfect small-set expanders; this allows noncommuting Pauli terms and uses no interaction geometry.
---

**ESTABLISHED (ordinary proof, unreviewed).** Let `H = sum_P beta_P P` be an explicit
real combination of Hermitian `n`-qubit Paulis, with weight `W = sum_P |beta_P|`,
and call `F = W - lambda_max(H) >= 0` its Pauli frustration. Then

```text
max_(phi stabilizer state) <phi|H|phi>  >=  lambda_max(H) - (1+sqrt2) F.      (SR)
```

The decomposition may list the same Pauli more than once, with either sign; the
proof treats each occurrence as its own term. The optimal constant lies in
`[1/sqrt2, 1+sqrt2]`: for `(X+Z)/2` the ratio `(lambda_max - stab_max)/F` equals
`1/sqrt2`. The sharp value is the open claim
`stabilizer-rounding-constant-is-one-over-sqrt2`.

**Model test.** On MSI, 7500 random instances with `n<=3` and exhaustive
stabilizer enumeration gave no violation of (SR) and a largest ratio of
`0.707107` (`research/artifacts/pauli-stabilizer-rounding-model-test-2026-09-12.md`).

**Idea.** In a top eigenvector, signed Paulis with expectation above `1/sqrt2`
pairwise commute, because two anticommuting ones sum to at most `sqrt2`.
Measure them jointly and keep a good sign pattern. Average over the stabilizer
states of that joint eigenspace, which are permuted by Paulis in the
centralizer; every term outside the generated group then averages to zero.
Terms with expectation at most `1/sqrt2` lose at most `(1+sqrt2)` times their
share of `F`.

**Consequences.** `pauli-projector-hamiltonians-are-stabilizer-approximable`
(a multiplicative `2+sqrt2` approximation for sums of Pauli projectors, and an
NP upper bound at ratio above `2+sqrt2`), and
`pauli-norm-games-qpcp-needs-imperfect-completeness` (the Pauli energy test of
games protocols).
