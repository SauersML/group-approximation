---
rg: 2
id: thompson-f-not-hyperlinear-from-llp-and-no-factorization
kind: route
title: LLP of C*(F) plus failure of the factorization property makes Thompson's F nonhyperlinear
target: thompson-f-is-not-hyperlinear
requires:
  - thompson-f-full-c-star-algebra-has-llp
  - thompson-f-lacks-factorization-property
  - llp-makes-hyperlinear-traces-amenable
---

**Neighbours.**
- `thompson-f-not-hyperlinear-via-nonsoficity-and-frames` consumes collapse of permutation models plus a
  masa-normalizing frame for unitary models. This route consumes collapse of compression (Stinespring)
  models plus a lifting property of `C*(F)`.
- `non-hyperlinear-from-llp-non-rf-kazhdan` combines LLP with Kirchberg rigidity for Kazhdan groups.
  This is the non-rigid analogue, where the factorization property must fail directly.

**Chain.** Suppose `F` is hyperlinear.
1. There is a trace-preserving embedding of `L(F)` into `R^omega`. Composing with `C*(F) -> L(F)` makes
   the canonical trace `tau_reg` on `C*(F)` a hyperlinear trace.
2. By `thompson-f-full-c-star-algebra-has-llp` and `llp-makes-hyperlinear-traces-amenable`, `tau_reg` is
   amenable.
3. That is the factorization property, contradicting `thompson-f-lacks-factorization-property`.

**Why the split is genuine.** Each premise can fail on its own.
- Amenability of `F` would make the first premise true and the second false.
- `F` hyperlinear without the factorization property would make the first premise false, since LLP
  would force the factorization property.

**Finitary form of the pair.**
- **Premise 2.** Uniform almost-commutation of compressions `P pi(.) P` of honest representations by
  almost-invariant projections (`thompson-f-factorization-iff-ucp-models-separate`).
- **Premise 1.** The route uses premise 1 only through this weaker consequence: every limit distribution
  of unitary almost-solutions of the two relators
  (`thompson-f-hyperlinear-iff-relator-system-hs-unstable`) is also a limit distribution of such
  compressions. That is, every hyperlinear trace on `C*(F)` is amenable.

**Obstruction for the compression class.** Every model built as a compression of a genuine
representation certifies at most premise 2. This covers Jones, Pythagorean, `O_2`/Cuntz, Koopman and
induced-representation compressions, and any ucp map on `C*(F)`.
- The invariant is the amenable/Connes-embeddable gap on `C*(F)`.
- The step where each member dies is the lifting of an arbitrary `R^omega`-valued homomorphism to ucp
  microstates.

A collapse theorem for such models proves nonhyperlinearity only through premise 1.
