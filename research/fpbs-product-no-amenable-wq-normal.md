---
rg: 2
id: fpbs-product-no-amenable-wq-normal
kind: claim
title: Nonamenable products with no infinite amenable wq-normal subgroup have strict thresholds on every Cayley graph
distinct_from:
  fpbs-no-amenable-wq-normal-class-nonuniqueness: that is the whole complementary class of nonamenable groups; this is its direct-product part, where two commuting nonamenable factors are available as a hypothesis.
  fpbs-product-every-generating-set: that is every nonamenable product; this is the case with no infinite amenable wq-normal subgroup, e.g. F_2 x F_2, where the relative-susceptibility reduction does not apply.
---

**OPEN.** Let `H` and `K` be infinite finitely generated groups such that
`G = H x K` has no infinite amenable wq-normal subgroup. Then every Cayley graph
of `G` has `p_c < p_u`. Both factors are then nonamenable, because an infinite
amenable `K` would give the normal subgroup `{1} x K`. Examples are `F_2 x F_2`
and products of nonelementary hyperbolic groups.

## Attempts

* **Nonuniqueness at `p_u`.** `fpbs-pu-nonuniqueness-commuting-subgroups`
  applies to every Cayley graph. **Where it stops:** that conclusion is weak,
  and `fpbs-pu-nonuniqueness-cannot-separate` shows the missing input is
  `theta(p_u) > 0`.
* **Relativize along a factor.** `N = H x {1}` is infinite and normal, so
  Hutchcroft--Pan Proposition 1.9 gives `p_u(N;G) = p_u(G)`. **Where it
  stops:** relative Burton--Keane (their Theorem 1.7) needs `N` amenable. The
  identity `p_c(N;G) = p_u(N;G)` used by
  `fpbs-bs-iff-finite-relative-susceptibility` is therefore unavailable.
* **Nonunimodular product structure.** A free-basis product generating set
  gives `T_k x T_l`, which `fpbs-hyperbolic-and-nonunimodular-nonuniqueness`
  covers. **Where it stops:** it does not cover mixed or non-free-basis
  generating sets (`fpbs-mixed-gen-set-not-cartesian`).
* **Effective non-approximability.** Gaboriau--Tucker-Drob Theorem 3.1 forces a
  sub-relation to fill the orbit relation. It needs connection probabilities
  above `1 - delta` along the generators of `H`. **Where it stops:** under
  collapse `theta(p)` tends to `0` as `p` decreases to `p_c`, so the hypothesis
  holds only at high parameters.
