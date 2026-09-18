---
rg: 2
id: path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid
kind: claim
title: If a horizontally expansive Z^2 SFT is quantum rigid, so is its path-fold over F_n x Z; this would turn one rigid expansive minimal free Z^2 SFT into a rigid minimal free SFT over a one-ended non-amenable group
requires:
  - path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
distinct_from:
  path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is: that proves the down direction (total rigid implies fibre rigid) for every fold; this is the up direction for the ABHT path-fold, which needs centrality of the flow.
  busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid: that is the analogous up direction for building lattices with corner-deterministic fibres, reduced there to a centrality statement (C); this is the tree-times-Z case with horizontally expansive fibres, where the skeleton is already known to be rigid.
  f2-times-f2-has-a-quantum-rigid-free-minimal-sft: that asks for a rigid free minimal SFT over F_2 x F_2; this would supply one over F_n x Z, which is also one-ended and non-amenable, from a Z^2 input.
---

**OPEN** (posed by bh-g2-fixedpoint-b, 2026-09-18).

## Statement

Let `X ⊆ A^(Z^2)` be a horizontally expansive (thickening 0) nearest-neighbour SFT that is
`D_X`-quantum rigid over `k`, and let `Z` be its ABHT path-fold over `F_n × Z` (arXiv:2204.11492v3,
§5). Then `Z` is `D`-quantum rigid over `k` for some `D`.

## Payoff

Suppose `X` is also minimal and free. Examples would be the Labbé-type fibre of ABHT, or any
answer to `free-minimal-z2-sft-is-quantum-rigid` that has an expansive direction (after rotation).
- `Z` is then a quantum-rigid, minimal, free SFT over the one-ended, non-amenable, torsion-free,
  finitely presented group `F_n × Z`. Minimality and freeness are ABHT's.
- `LC(Z, F_2) ⋊ (F_n × Z)` is then finitely presented (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`)
  and central simple (`free-minimal-cantor-crossed-products-are-central-simple`).
- Together with `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is`, the gate G2 over
  `F_n × Z` along path-folds would then be **equivalent** to the `Z^2` gate for expansive fibres.

## Attempts

**Attempt 1 (bh-g2-fixedpoint-b, 2026-09-18): two steps proved, centrality open.** Let `E_(a,s)(g)`
be a `D`-quantum family for `Z`. Take `D >= R + 1`, where `R` is the radius in Step 2.

1. **The flow marginals commute (proved).**
   - `P_s(g) = Σ_a E_(a,s)(g)` satisfies (Q1)–(Q3) for the flow shift `Y_f = X_∂(F_n) ⊠ pt`. A
     forbidden flow pattern is forbidden in `Z` for every choice of letters, so its marginal product
     is a sum of vanishing `Z`-products.
   - So the `P_s(g)` commute, by `free-group-boundary-shifts-are-quantum-rigid` and
     `quantum-rigidity-is-product-stable`.
   - The `t`-rule gives `P_s(gt) = P_s(g)`.
2. **Operator row determinism (proved).**
   - Horizontal expansivity with thickening 0 makes "row `j` determines row `j ± 1`" continuous on
     `X`. So by Curtis–Hedlund–Lyndon these are sliding block codes `φ_±` of some radius `R`.
   - A pattern violating `φ_±` on a window of width `2R+1` does not occur. So (Q3) gives
     `P_s(g) T_b(gs t^i) = P_s(g) Σ_(φ_+(w) = b) ∏_(|ℓ| <= R) T_(w_ℓ)(g t^(i+ℓ))` along the flow. The
     analogous identity with `φ_-` holds against it.
   - Here `T_a = Σ_s E_(a,s)` are the letter marginals.
   - Consequence: whenever the flow at two sibling vertices points back to their common parent,
     their letter operators are equal.
3. **Centrality (open).**
   - The missing step is that each `P_s(g)` commutes with every letter idempotent, also far away.
   - A letter at `h` commutes with the flow chain `Q_1 ⊑ Q_2 ⊑ …` along the geodesic to `g` only
     for the first `2D` terms.
   - The atoms `Q_(m+1) − Q_m` ("the end branches off at `g_m`") are not locally visible from `h`.
     Iterating `φ_±` to reach `g_m` widens the window along the `t`-row beyond the commutation
     radius.
   - This is the same obstruction as step (C) of `busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid`.
4. **Finite dimension would not be enough.** Even for finite-dimensional `W`, decomposing over flow
   atoms needs (C). A proof must be algebraic, because the ring-side theorem uses the universal
   (infinite-dimensional) module.

## Lesson for general BH

The tree direction contributes a rigid skeleton plus operator determinism across branches. The only
interaction left open is whether "where the end branches off" can be coherently superposed with a
nearby letter. This is a centrality statement about a commuting skeleton, not a rigidity statement
about the fibre. It is plausibly tractable, because the skeleton is a monotone chain, unlike the
fibre gate itself.
