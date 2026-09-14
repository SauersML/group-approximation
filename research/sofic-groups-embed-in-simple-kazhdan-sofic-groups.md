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
  - **Overgroup found (sk-perfect-overgroup, 2026-09-13, unreviewed).** The half-line overgroup
    `C(Γ) = E ⋊ Z ≤ Sym(Γ × Z)` is sofic when `Γ` is (`E` is a directed union of finite powers, and Elek–Szabó give
    permanence), and `Γ ≤ [C(Γ), C(Γ)]` (`groups-embed-in-derived-subgroup-of-half-line-overgroup`). So this gate is
    closed for every finitely generated sofic `Γ`. What still remains: Hamming soficity of a non-LEF envelope, and for
    non-amenable `Γ` a measured free minimal subshift over `C(Γ)`.
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
  For the rank route this is superseded by the lamplighter host in the next bullet.
- **All sofic inputs, rank metric (sk-measured-subshift, 2026-09-13, unreviewed).**
  - Every finitely generated sofic `Γ` is a subgroup of an infinite finitely generated simple Kazhdan `F_2`-linear
    sofic group (`sofic-groups-embed-in-simple-kazhdan-linear-sofic-groups`).
  - The host is the lamplighter action of `Z/2 ≀ C(Γ)` on `2^(C(Γ))`. Its crossed product has counting rank models
    over sofic approximations (`sofic-lamplighter-bernoulli-crossed-products-have-rank-models`).
  - So the measured free minimal subshift is not needed for the rank route, and what remains of this claim is the
    rank-to-Hamming gap.
- **Ultraproduct envelopes directly.** Inside a rank ultraproduct `∏_ω M_(N_k)(F_2)` the image of a
  sofic group is available at once. But a finitely generated simple subring with local annihilation
  containing it must still be produced. Paradoxical rings such as Leavitt algebras are excluded,
  because the rank function is stably finite, so this route returns to crossed products.
- **Permanence closure: dead for the hosts (sk-sofic-host-hamming, 2026-09-13, unreviewed).**
  - Start from amenable and LEF groups and close under subgroups, directed unions, finite products, amenable
    extensions, graphs of groups, and marked limits. That closure holds amalgams over amenable subgroups, graph
    products and wreath products with amenable top. Every finitely generated Kazhdan group in it is LEF
    (`kazhdan-groups-in-sofic-permanence-closure-are-lef`). The finitely presented case, with residual finiteness, is
    `lea-permanence-closure-fp-kazhdan-groups-are-residually-finite` (sk-fp-sofic-host). The hosts are not finitely
    presented, so they need the finitely generated form.
  - So the host of a non-LEF input (for example `BS(2,3)`) needs soficity from a source that is not a permanence
    operation.
  - **Orbit full groups.** If the action has exactly equivariant finite models (profinite actions, Bernoulli shifts of
    LEF groups, the dual actions of the LEF hosts), every finitely generated subgroup of its full group is LEF
    (`research/artifacts/sk-sofic-host-hamming-2026-09-13-part1.md` §4). With
    `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`, the only live full-group seeds are non-amenable, non-LEF
    sofic actions with inexact models.
- **What would settle it.** Either a sofic approximation of some `EL_n(R)/Z` that is not a local
  embedding, which by the barrier above must avoid all algebraic targets; or a proof that sofic
  infinite simple Kazhdan groups are LEF, which would refute the statement for every non-LEF sofic
  input.
