---
rg: 2
id: o2-ideal-finite-nucdim-counterexample-unital-quotients-proof
kind: route
title: Robert's stability criterion plus trace vanishing under O_2 self-similarity
target: o2-ideal-finite-nucdim-counterexample-unital-quotients
requires: [k1-injectivity-extends-over-properly-infinite-quotients, o2-multiplier-extension-k1-injective-iff-unitization]
artifacts:
  - research/artifacts/k1-o2-ideal-finite-nuclear-dimension-2026-09-13.md
---

Full proofs are in the artifact, sections 2 and 3.

- **Traces.** `τ(S_i x S_i^*) = τ(x)`, so `2τ(e_λ) <= ||τ||` along an approximate unit, which forces `τ = 0`.
- **Stable ideals.** Compress to `M_n(J)~` and use the room in `1 - e_n` to absorb the stabilization.
- **Robert.** L. Robert, arXiv:1002.2180v2, Corollary 1, verified from the PDF: a σ-unital hereditary
  `B ⊆ A ⊗ K`, with `A` of nuclear dimension at most ω, is stable iff it has no nonzero unital quotients
  and no nonzero bounded traces.
- **Unital quotients.** The unit of `I/K` is central in `A/K`, with complement `A/I = O_2`.
- **Largest stable part.** Ideals with no unital quotient are closed under finite sums and closed
  increasing unions. The extension lemma `k1-injectivity-extends-over-properly-infinite-quotients` passes
  K1-injectivity from `A/J_0` up to `A`. The iff theorem for `O_2`-extensions transfers it to `(I/J_0)~`.
