---
rg: 2
id: sofic-groups-embed-in-simple-kazhdan-sofic-groups
kind: claim
title: Every finitely generated sofic group embeds in an infinite simple Kazhdan sofic group
distinct_from:
  amenable-perfect-groups-embed-in-kazhdan-linear-sofic: that is proved for perfect amenable inputs with a linearly sofic envelope; this asks for soficity and for all sofic inputs.
  rf-groups-embed-in-simple-kazhdan-lef-groups: that is the residually finite case, where the envelope is LEF; soficity of the input allows non-LEF groups, which no LEF envelope can contain.
  free-minimal-subshift-elementary-groups-are-sofic: that asks whether one concrete family is sofic; this asks for envelopes containing a prescribed sofic group.
---

**OPEN.** For every finitely generated sofic group `Γ` there is an infinite simple group with
property (T) that is sofic and contains `Γ`. Soficity passes to subgroups, so the finitely generated
sofic groups would then be exactly the finitely generated subgroups of infinite simple Kazhdan sofic
groups.

## Attempts

- **Cost of the statement.** It implies a sofic infinite simple Kazhdan group that is not LEF
  (`sofic-universal-envelope-forces-non-lef-simple-kazhdan`, reviewed PASS). No such group is known.
- **Embedding step.** Units of `LC(X,k) ⋊ Δ` enter `EL_3` only on `[Δ,Δ]`, and `K_1` is the exact
  obstruction (`perfect-groups-embed-in-crossed-product-elementary-groups`). So the input must sit in
  the derived subgroup of the acting group.
  - **Dead route:** the swap double `(Γ×Γ)⋊C_2` with `γ ↦ (γ,γ^(-1))` is not a homomorphism for
    nonabelian `Γ` (sk-verify-4 FAIL on `double-swap-embeds-group-in-derived-subgroup`).
  - **Dead route:** wreath products keep the abelianization of the base
    (`wreath-products-keep-the-abelianization-of-the-base`).
  - **What remains:** for non-perfect `Γ`, an overgroup `Δ` in the same class with `Γ ⊆ [Δ,Δ]`
    is needed. Ore's theorem gives one only for residually finite groups.
- **Perfect amenable inputs, rank metric.** A free minimal subshift and the Folner rank model give a
  simple Kazhdan linearly sofic envelope (`amenable-perfect-groups-embed-in-kazhdan-linear-sofic`).
  The envelope is not LEF when the input is not, so the gap between the rank and Hamming metrics is
  the whole remaining content.
- **Rank to Hamming: blocked.** By `gap-sofic-approximations-are-local-embeddings`, models of
  `EL_n(R)` through `GL_N(F_q)` on vectors, affine spaces or lines turn a rank defect `r` into a
  Hamming defect `1 - q^(-O(r))`. They are sofic approximations only when exactly multiplicative,
  that is, only when they witness LEF. The same barrier is recorded for the `Z^2` family in
  `free-minimal-subshift-elementary-groups-are-sofic`.
- **Non-amenable acting groups: the Folner step fails.** The rank model truncates the orbit
  representation to Folner sets. The replacement is a labelling of sofic approximation graphs by
  points of `X` that is equivariant off a vanishing set. It needs an invariant measure on a free
  minimal `X` and a sofic orbit relation; the missing input is
  `sofic-groups-have-measured-free-minimal-subshifts`. The conditional rank bound is written in
  `research/artifacts/sk-sofic-embedding-b-ultraproduct-envelopes-2026-09-13.md` §4.
- **Ultraproduct envelopes directly.** Inside a rank ultraproduct `∏_ω M_(N_k)(F_2)` the image of a
  sofic group is available at once. But a finitely generated simple subring with local annihilation
  containing it must still be produced. Paradoxical rings such as Leavitt algebras are excluded,
  because the rank function is stably finite, so this route returns to crossed products.
- **What would settle it.** Either a sofic approximation of some `EL_n(R)/Z` that is not a local
  embedding, which by the barrier above must avoid all algebraic targets; or a proof that sofic
  infinite simple Kazhdan groups are LEF, which would refute the statement for every non-LEF sofic
  input.
