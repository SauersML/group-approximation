---
rg: 2
id: mf-min-tensor-exact-stably-finite-is-stably-finite
kind: claim
title: The spatial tensor product of an MF algebra with an exact algebra with stably finite unitization is stably finite
distinct_from:
  mf-min-tensor-exact-mf-is-mf: that assumes the second factor is MF and concludes MF; this assumes only exactness and stable finiteness of the second factor and concludes stable finiteness, which is what refutes the tensor-infiniteness certificate for nuclear algebras with faithful traces.
  nuclear-factor-with-infinite-mf-tensor-exists: that is the certificate asking for an MF algebra and a nuclear faithful-trace algebra with infinite spatial tensor product; this is the theorem showing that no such pair exists.
  hyperfinite-factor-not-quasidiagonal: that is Ozawa's MF algebra with an infinite spatial tensor product with R; this shows the second factor there must be non-exact, since every exact subalgebra of R has a faithful trace.
artifacts:
  - research/artifacts/uct-nuclear-proper-isometry-2026-09-12.md
---

**ESTABLISHED (derivation `mf-min-tensor-exact-stably-finite-proof`).** Let `A`
be an MF C\*-algebra and let `C` be an exact C\*-algebra whose unitization
(`C` itself when unital) is stably finite. Then `A ⊗_min C` is stably finite.

**Corollaries.**
- **The certificate is refuted.** A nuclear `C` with a faithful tracial state is
  exact, and its unitization carries the extended faithful trace, so it is stably
  finite. So `A ⊗_min C` is stably finite for every MF `A`. This refutes
  `nuclear-factor-with-infinite-mf-tensor-exists`, and the route
  `nuclear-non-uct-via-infinite-mf-tensor` dies with it.
- **Ozawa's example forces a non-exact second factor.** Every separable exact
  C\*-subalgebra `C` of `R` (or of any finite von Neumann algebra with a faithful
  normal trace) keeps `A ⊗_min C` stably finite for every MF `A`. So Ozawa's
  proper isometry (`hyperfinite-factor-not-quasidiagonal`) lies in `A ⊗_min C`
  only for non-exact `C`.

**No UCT input.** The proof uses only Kirchberg's definition of exactness, polar
decomposition and finiteness in each matrix block. It does not go through
Tikuisis--White--Winter, so the refutation is not circular for the UCT problem.

Credit: a small variant of the Blackadar--Kirchberg permanence argument behind
`mf-min-tensor-exact-mf-is-mf`, and very likely known. No novelty is claimed,
and the literature was not searched for a printed statement.
