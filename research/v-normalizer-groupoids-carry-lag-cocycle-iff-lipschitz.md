---
rg: 2
id: v-normalizer-groupoids-carry-lag-cocycle-iff-lipschitz
kind: claim
title: For t of infinite order in Out(V), the germ groupoid of V ⋊ ⟨t⟩ is the semidirect product of the Cuntz groupoid by t, and its lag cocycle extends continuously exactly when t is Lipschitz
distinct_from:
  v-normalizer-rsgs-contract-iff-finite-outer-order: that proves V ⋊ ⟨t⟩ is a finitely presented, non-contracting, non-full RSG; this identifies the germ groupoid whose topological full group is the full closure, and decides when it is Z-graded by lag.
  out-v-contains-the-root-problem-for-the-full-2-shift: that identifies the Lipschitz part L_2 of Out(V) with the inert automorphisms of the full 2-shift; this shows L_2 is exactly where the lag grading survives.
artifacts:
  - research/artifacts/gq-gq-infinite-primes-out-v-reading.md
---

**ESTABLISHED** through `v-normalizer-groupoids-carry-lag-cocycle-iff-lipschitz-proof`.
Lane proof (bh-higman-classic), elementary, not independently reviewed. No priority claimed.

## Setting

`C = {0,1}^N`. `O` is the groupoid of germs of `V` (the Cuntz groupoid of `O_2`). Its
*lag* cocycle `ℓ : O → Z` sends the germ of a prefix replacement `uω ↦ u'ω` at `uω` to
`|u| - |u'|`. Let `t ∈ N(V)` have infinite order in `Out(V)`, `Γ_t = V ⋊ ⟨t⟩`, and let `G_t`
be the groupoid of germs of `Γ_t`. Then `[[Γ_t]]` is the topological full group of `G_t`.

## Statement

1. **Semidirect product.** Conjugation by `t` is an automorphism `α_t` of `O` covering the
   homeomorphism `t` of `C`, and `(g, n) ↦ [g] · [t^n]` is an isomorphism of étale groupoids
   `O ⋊_{α_t} Z ≅ G_t`. In particular no germ of `t^n`, `n ≠ 0`, lies in `O`.
2. **Lag extends iff Lipschitz.** There is a continuous cocycle `c : G_t → Z` with `c|_O = ℓ`
   if and only if the core of `t` satisfies the Lipschitz constraint (every circuit outputs a
   word of the same length as its input), that is, iff the class of `t` lies in
   `L_2 ≅ Inert(σ_2)`. In that case `c([t], x) = -K_t(x_1 … x_k)` for an explicit function
   `K_t` of the first `k` letters, where `k` is the synchronizing level of `t`.

## Reading

For Lipschitz `t`, `G_t` is Z-graded like an SFT groupoid, but its degree-zero part contains
the germs of `t` corrected to lag zero. So it is the tail groupoid of the full 2-shift
extended by the inert automorphism, a "rank-two" analogue of the Cuntz groupoid built from
the commuting pair `(σ, F)`. For non-Lipschitz `t` there is no continuous lag grading at all.
This separates the two natural sub-questions of `fp-rsgs-have-fp-full-closures` for the
family `Γ_t`.
