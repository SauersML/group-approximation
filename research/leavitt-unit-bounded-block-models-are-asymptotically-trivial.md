---
rg: 2
id: leavitt-unit-bounded-block-models-are-asymptotically-trivial
kind: claim
title: Block-monomial HS models of the binary Leavitt unit group with small block size times squared defect converge to the identity
distinct_from:
  leavitt-units-admit-no-bounded-block-monomial-hs-model: that excludes regular models with a fixed block size and makes every model block-diagonal; this drops regularity and injectivity and proves pointwise convergence to the identity whenever block size times squared defect tends to zero, so bounded-block models carry nothing at all.
  block-monomial-hs-models-sofic-mod-amenable-soft-kernel: that bounds the soft kernel of a regular bounded-block model of an arbitrary group; this uses the full MF radical of one simple group to kill the block labels of every model below the displayed size threshold, with no trace hypothesis.
  binary-leavitt-unit-group-hyperlinear: that asks whether Hilbert--Schmidt models exist at all; this shows that any nontrivial model needs blocks at least of order the inverse squared multiplicative defect, a regime that a single block of full dimension always occupies.
---

**ESTABLISHED.**  Let `R = L_(F_2)(1,2)` and `U = R^x`.  For each `m` let
`rho_m : U -> U(k_m) wr S_(n_m)` act block-monomially on
`C^(n_m) ⊗ C^(k_m)`, with normalized Hilbert--Schmidt norm
`||X||_2^2 = tr(X^* X)`, and put
`eps_m(g,h) = ||rho_m(gh) - rho_m(g) rho_m(h)||_2`.  Assume

```text
eps_m(g,h) -> 0   and   k_m * eps_m(g,h)^2 -> 0     for all g, h in U.   (BB)
```

Then `||rho_m(g) - 1||_2 -> 0` for every `g in U`.

- **Fixed block size.**  (BB) holds automatically when `k_m = k` is
  constant.  So every HS asymptotic homomorphism of `U` into `U(k) wr S_n` is
  asymptotically trivial, and `U` has no injective bounded-block monomial HS
  model, regular or not.  The regular case is already
  `leavitt-units-admit-no-bounded-block-monomial-hs-model` clause 2.
- **Size threshold.**  An injective block-monomial HS model of `U` must have
  `limsup_m k_m eps_m(g,h)^2 > 0` for some pair `(g,h)`: blocks at least of
  order `eps^-2`.  One block of full dimension, meaning an arbitrary HS
  microstate, sits in that regime.  So below the threshold the bounded-block
  question is settled, and at or above it the question is
  `binary-leavitt-unit-group-hyperlinear` itself.

This is a short corollary of trace-free block-diagonality and full MF radical.
Its new content is dropping the regularity and injectivity hypotheses and the
explicit size threshold.

## Attempts

Established; see `leavitt-unit-bounded-block-triviality-via-mf-radical`.
