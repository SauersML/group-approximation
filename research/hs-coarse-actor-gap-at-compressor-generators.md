---
rg: 2
id: hs-coarse-actor-gap-at-compressor-generators
kind: claim
title: The approximate actor has a coarse gapped block decomposition at vertex and compressor generators, compatible with the rounded vertex center
distinct_from:
  hs-one-level-expander-block-decomposition: that asks for a one-level decomposition of one Kazhdan group at its own generators, with no compressor and no compatibility with another algebra; this asks for the actor at a generating set containing strict compressors, with blocks almost commuting with the center of the rounded vertex commutant uniformly over block-dependent central contractions.
  nonmonomial-multiplicity-obstructs-hs-compressor-transport: that shows no universal compressor transport clause can be appended to a block decomposition; this asks for no transport clause, since transport is supplied by vertex rounding.
  hs-normalization-needs-coarse-actor-scale-pinning: that is the open conditional whose clause (H2) this makes precise; this is only the block-decomposition input, stated for every model.
  hs-rounding-and-actor-gap-force-ccr: that is the proved conditional which assumes (H2') for one model and derives normalization; this is (H2') itself, for every model, and nothing proved decides it.
---

**OPEN.** Let `Gamma < G` be an infranormal, non-normal pair of Kazhdan groups, with `(F, kappa)` a Kazhdan
pair for `Gamma`. There are strict compressors `t_1, ..., t_k` with `G = <Gamma, t_1, ..., t_k>`, and
`S = F cup {t_i^(+-1)}`, such that the following holds. For every trace-preserving `sigma : G -> U(prod_U M_n)`
satisfying (H1) (`hs-stable-vertex-rounding-for-every-model`), and every rounding `pi_n` witnessing it, there
are, along `U`, orthogonal projections `q_A` with `p = sum_A q_A` and a constant `kappa' > 0` with:

- (a) `tau(1 - p) -> 0`, and `sum_A ||[sigma_n(s), q_A]||_2^2 -> 0` for each `s in S`;
- (b) for every `A` and every self-adjoint `x in q_A M q_A`,
  `sum_(s in S) ||a_(A,s) x - x a_(A,s)||_(2,q_A)^2 >= kappa'^2 ||x - tau_(q_A)(x) q_A||_(2,q_A)^2`, where
  `a_(A,s) = q_A sigma_n(s) q_A`;
- (c) `sup sum_A ||[q_A, z_A]||_2^2 -> 0`, the supremum over families of contractions `z_A` in the center of
  `pi_n(Gamma)'` chosen block by block.

This is hypothesis (H2') of `hs-rounding-and-actor-gap-force-ccr`, required for every model.

## Attempts

- **Cascades.** Under (H1), a multiplicity cascade with order-one jump mass
  `tau(zeta_B >= 2 zeta_A)` refutes this claim, by `hs-rounding-and-actor-gap-force-ccr` and
  `commutant-excess-bounded-by-aspect-ratio-jump-mass`. Such a cascade needs a slowly varying, ungapped
  almost-central observable of the actor that the compressors shift, i.e. Hilbert-hotel surgery on
  boundary levels compatible with the relations of `G`. Genuine `G`-models exclude it
  (`ccr-holds-for-all-genuine-fd-coordinate-models`). No cascade model for a Theorem E actor is known.
- **Blocks from the literal actor commutant.** Dead, for the same reason as the vertex case
  (`hs-literal-commutant-profile-rounding-is-false`). The blocks must come with a gap, not as a center.
- **Fixed-scale center clause.** Too weak. Almost commutation with `F_a(zeta_A)` for one `a` at a time
  does not control a median observable whose scale varies from block to block. A rank-one block
  half on two isotypic components where `F_m = 0.2` and `0.8` has compression `1/2` and no mass near
  scale `m` (artifact `hs-s4-assembly-2026-09-12.md`, section 6). Hence (c).
- **One Kazhdan group.** Even the one-level decomposition at a group's own generators is open
  (`hs-one-level-expander-block-decomposition`). (b) needs it for the actor at `S`, with a gap that sees
  the compressors.
- **Compressor transport clause.** Not asked, and not appendable in general
  (`nonmonomial-multiplicity-obstructs-hs-compressor-transport`). Transport comes from (H1) through the
  intertwiner of `vertex-rounding-reduces-ccr-to-commutant-excess`.
