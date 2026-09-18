---
rg: 2
id: fpbs-residual-class-via-percolation-kesten-split
kind: route
title: Residual class via the normal nonamenable-quotient split
target: fpbs-residual-price-one-non-ah-class-nonuniqueness
requires:
  - fpbs-percolation-kesten-normal-gap
  - fpbs-normally-coamenable-class-nonuniqueness
  - fpbs-relative-gap-along-any-subgroup-separates
---

Let `Gamma` be in the residual class. It is nonamenable, so the dichotomy of
`fpbs-bs-via-percolation-kesten-split` applies.

- **(α) Some infinite normal `N` has nonamenable quotient.**
  `fpbs-percolation-kesten-normal-gap` gives `p_c(G) < p_c(N;G)`, and
  `fpbs-relative-gap-along-any-subgroup-separates` then gives `p_c < p_u`.
- **(β) Otherwise.** `Gamma` is normally co-amenable, and
  `fpbs-normally-coamenable-class-nonuniqueness` gives `p_c < p_u`. ∎

**How the known members fall.**

- **Case (α).** The products `T x T'` of torsion Tarski monsters and
  `B(m,n) x B(m',n')`, which make up the product class of
  `fpbs-product-no-amenable-wq-normal`, all lie in (α), taking `N` to be a
  factor.
- **Case (β).** A single torsion Tarski monster is simple, so it lies in (β),
  if it has fixed price one. There no relative-threshold argument is available
  (`fpbs-relative-threshold-commensurability-invariant`).
- **Not placed here.** This route does not decide whether a single `B(m,n)`
  lies in (α) or (β).

**Honest scope.** Premise (β) is stated for the whole normally co-amenable
class, which is more than the residual class needs. What this route adds is
that, on the residual class, the products and every other member with a
nonamenable normal quotient reduce to the single percolation statement (α).
