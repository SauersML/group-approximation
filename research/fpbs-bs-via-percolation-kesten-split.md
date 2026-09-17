---
rg: 2
id: fpbs-bs-via-percolation-kesten-split
kind: route
title: Split every nonamenable group by whether some infinite normal subgroup has nonamenable quotient
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-percolation-kesten-normal-gap
  - fpbs-normally-coamenable-class-nonuniqueness
  - fpbs-relative-gap-along-any-subgroup-separates
---

Let `Gamma` be nonamenable and finitely generated, `S` a finite symmetric
generating set, and `G = Cay(Gamma,S)`. Exactly one of the following holds.

**(α) Some infinite normal subgroup `N` has nonamenable quotient `Gamma/N`.**
By `fpbs-percolation-kesten-normal-gap`, `p_c(G) < p_c(N;G)`. Since `N` is an
infinite subgroup, condition 1 of
`fpbs-relative-gap-along-any-subgroup-separates` holds, and so
`p_c(G) < p_u(G)`.

**(β) Every infinite normal subgroup has amenable quotient.** Then `Gamma` is
normally co-amenable, and `fpbs-normally-coamenable-class-nonuniqueness` gives
`p_c(G) < p_u(G)`.

The dichotomy is exhaustive by definition. ∎

**Design notes.**

- **Independent prerequisites.** The two open premises can fail on their own
  (see the independent-failure-modes paragraph of
  `fpbs-normally-coamenable-class-nonuniqueness`).
- **Premise (α) is a single percolation statement.** It already implies these
  open roots:
  - `fpbs-product-every-generating-set`, through
    `fpbs-product-every-generating-set-via-percolation-kesten`;
  - `fpbs-hyperbolic-quotient-every-generating-set`, through
    `fpbs-hyperbolic-quotient-via-percolation-kesten`;
  - the normal-subgroup case of the amenable-kernel class.
- **Premise (β) lies where no normal relative threshold exists.** Inside it,
  on groups whose infinite subgroups all have finite index, no relative
  threshold exists at all (`fpbs-relative-threshold-commensurability-invariant`).
