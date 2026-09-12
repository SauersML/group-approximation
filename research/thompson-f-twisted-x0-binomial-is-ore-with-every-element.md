---
rg: 2
id: thompson-f-twisted-x0-binomial-is-ore-with-every-element
kind: claim
title: In the group ring of Thompson's group F over any field, 1 + lambda x_0 has a nonzero common right multiple with every nonzero element, for every nonzero scalar lambda
distinct_from:
  thompson-f-one-minus-x0-is-ore-with-every-element: that is the case lambda = -1 (Guba 2022); this is every nonzero lambda, obtained by weighting the orbit test at t = -1/lambda.
  thompson-f-binomial-pairs-have-common-multiples: that concerns augmentation binomials 1 - a and 1 - c and binomial b; this is the twisted binomial 1 + lambda x_0 against every element.
---

**ESTABLISHED.** Let `K` be a field, `R = K[F]`, and `lambda` in `K^x`. For every nonzero
`b` in `R`, `(1 + lambda x_0) R ∩ b R ≠ 0`.

For `lambda = -1` this is Guba's Theorem 2 of arXiv:2201.02308
(`thompson-f-one-minus-x0-is-ore-with-every-element`). The proof here follows Guba's
reduction to `K[M_1]` and the shift by `x_0`, with two changes:
- the coset test is weighted by powers of `mu = -1/lambda`;
- Guba's Theorem 3 (non-freeness of `{phi^k(b)}`) is replaced by a dimension count.

**Consequence.** Over infinite fields, Guba's systems `Q_k` contain forms
`alpha x_0 + beta x_1` with arbitrary ratio. Their principal right ideals are
`(1 + lambda g) R` for conjugates `g` of `x_0^{+-1}`-type elements. The twisted case is
what `thompson-f-rescaled-x0-binomials-have-common-multiples` needs to handle them.

**Scope.** Novelty is not claimed beyond the routine twist of Guba's argument.

Proof route: `thompson-f-twisted-x0-binomial-is-ore-with-every-element-proof`.
