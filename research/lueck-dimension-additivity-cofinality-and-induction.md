---
rg: 2
id: lueck-dimension-additivity-cofinality-and-induction
kind: claim
title: Lück's von Neumann dimension of arbitrary modules is additive, cofinal and invariant under induction
---

**ESTABLISHED (literature import).** For every group `G` there is a unique dimension function
`dim_(N(G))` on all `N(G)`-modules, with values in `[0, ∞]`, extending the trace dimension of
finitely generated projective modules, such that:
- **additivity:** `dim M_1 = dim M_0 + dim M_2` for every short exact sequence
  `0 -> M_0 -> M_1 -> M_2 -> 0`;
- **cofinality:** if `M` is the directed union of submodules `M_i`, then `dim M = sup_i dim M_i`;
- **induction:** for an injective homomorphism `i : H -> G`, the functor
  `M ↦ N(G) ⊗_(N(H)) M` is faithfully flat and `dim_(N(G))(N(G) ⊗_(N(H)) M) = dim_(N(H)) M`.

**Consequences used downstream.**
- Submodules, quotients and countable direct sums of dimension-zero modules have dimension zero.
- For `H <= G` and `β_t^(2)(H) = dim_(N(H)) Tor_t^(ZH)(N(H), Z)`: by flatness
  `Tor_t^(ZH)(N(G), Z) ≅ N(G) ⊗_(N(H)) Tor_t^(ZH)(N(H), Z)`, so
  `dim_(N(G)) H_t(H; N(G)) = β_t^(2)(H)`.

Route: `lueck-dimension-additivity-induction-citation`.
