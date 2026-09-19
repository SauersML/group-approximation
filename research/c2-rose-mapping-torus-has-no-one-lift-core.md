---
rg: 2
id: c2-rose-mapping-torus-has-no-one-lift-core
kind: claim
title: For the admissible (C2) pair, the fibred K(G,1) (the mapping torus M_f of the rose representative of phi on F_4) cannot realize RP(H,G). The generator of H_2 of the H-cover is an explicit 7-cell cycle with two lifts of one 2-cell, certified by an index-9 cover. The same test excludes all 57,725 roses within three Nielsen moves of the standard basis
distinct_from:
  two-cell-injective-maps-realize-relative-eg-pairs: that proves RP(H,G) iff some 2-dimensional K(G,1) X receives a 2-cell-injective map from a K(H,1). This adds a canonical-cycle test that decides a given X. The unique generator of Z_2(X_H) must have support that injects into the 2-cells of X, and pushing it into finite covers gives finite certificates. The test is then applied to the fibred complexes of (C2).
  c2-one-relator-lift-presentations-are-obstructed: that closes two-generator one-relator relative presentations of H, which live over the presentation complex of <x,y|w>. This closes realizations inside a different K(G,1), the fibred rose mapping torus with four 2-cells, and its Nielsen neighbours.
  c2-slide-route-passes-every-relation-module-test: that shows module invariants cannot decide the slide route, which works through new presentations of G. This works inside a fixed K(G,1), where the obstruction is a single cycle and needs no module theory.
---

**ESTABLISHED** through `c2-rose-mapping-torus-has-no-one-lift-core-proof`. Unreviewed.
Parts (T0)–(T2) are proved by hand. (T3) is exact finite computation: memberships in `N` are
proved by fixed windows `T_M ⊂ N`, and non-memberships by one permutation representation
`G → S_9`. `experiments/c2-mapping-torus-2026-09-18/verify_cycle.py` replays it in under two
seconds. (T4) is an exhaustive computation, and it covers only the bases it lists.

## Setting

This is the pair of `admissible-ab-nonzero-two-cell-base-exists`:
- the group is `G = ⟨x,y | w⟩` with `w = yxYXXyyxYXYxYYxyXy`, and `G = F_4 ⋊_φ ⟨y⟩` with
  `F_4 = ⟨p,q,r,s⟩ = ⟨x_{-2},x_{-1},x_0,x_1⟩` and `x_j = y^j x y^{-j}`;
- `φ(z) = y z y^{-1}`, so `p ↦ q ↦ r ↦ s ↦ x_2 = rrSqPRs`;
- `H = ⟨XyxYx, Xyyyx, XYxyx, y, xyX⟩ = N ⋊ ⟨y⟩`, with `N = H ∩ F_4`;
- `ρ(H,G) ∈ {0,1}`, and `ρ = 0` is exactly `RP(H,G)`.

By `two-cell-injective-maps-realize-relative-eg-pairs`, `RP(H,G)` holds iff some 2-dimensional
`K(G,1)` `X` carries a 2-cell-injective combinatorial map `K → X` from a 2-dimensional `K(H,1)`
that induces `H ↪ G`. It is enough to find a subcomplex `C` of the cover `X_H` with
`π_1 C ≅ H` and at most one lift of each 2-cell of `X`.

## Statement

- **(T0) Canonical-cycle test.** Let `X` be any aspherical 2-complex with `π_1 X = G`, and `H ≤ G`.
  - `Z_2(X_H) = H_2(H)`.
  - If some 2-cell-injective map `K → X` from a `K(H,1)` induces `H ↪ G`, then every cycle in
    `Z_2(X_H)` has support that maps injectively to the 2-cells of `X`. The same holds for a
    subcomplex `C ⊂ X_H` whose inclusion induces `π_1 C ≅ H`.
  - For every finite-index `L ⊇ H`, the pushforward of such a cycle to `X_L` has at most one
    nonzero cell over each 2-cell of `X`.
- **(T1) Fibred complexes.** Let `f: Γ → Γ` be a graph map representing `φ` (a marked graph of
  `F_4`), and let `M_f` be its mapping torus. Then `Z_2((M_f)_H)` is the group of `f_N`-invariant
  1-cycles of the `N`-cover `Γ_N`, and this group is `H_1(N)^φ ≅ Z`. Each 2-cell of `(M_f)_H` is
  indexed by an edge of `Γ_N`.
- **(T2) The cycle.** Let `Γ` be the rose on `p,q,r,s`, and write `P̃[a]` for the lift at the vertex
  `Na` of the 2-cell `y p y^{-1} q^{-1}`, and likewise for the other cells. The generator of
  `Z_2((M_f)_H)` is
  `z = −2P̃[1] + P̃[s⁻¹] + 2R̃[1] − 2R̃[q⁻¹] + R̃[s⁻¹] + 2S̃[q⁻¹] − S̃[s⁻¹]`.
  It is the 1-cycle of `−[Q x_2] + [X_2 s x_2] − 2[pQ] − 2[qR]` in `Γ_N`. Its image in `M_f` is
  the relator class `S + R − P`, and its coefficient on every `Q`-cell is `0`.
- **(T3) Certificate.** The cosets `N`, `Ns⁻¹` and `Nq⁻¹` are pairwise distinct. The map
  `x ↦ (3,4,6,5)(7,8,9)`, `y ↦ (1,2,3)(5,7,8)` defines `G → S_9`, `H` fixes the point `4`, and
  `s⁻¹` and `q⁻¹` send `4` to `2` and `1`. So `z` pushed to the index-9 cover `X_L`, with
  `L = Stab(4)`, is `−2P̃_4 + P̃_2 + 2R̃_4 − 2R̃_1 + R̃_2 + 2S̃_1 − S̃_2`.
- **Consequence.** `M_f` carries no realization of `RP(H,G)`. Any subcomplex of `(M_f)_H` whose
  inclusion induces `π_1 ≅ H` contains at least 2 lifts of the `P`-cell, 3 of the `R`-cell and 2 of the
  `S`-cell. The same holds for the image of any combinatorial map `K(H,1) → M_f` that induces
  `H ↪ G`.
- **(T4) Nielsen neighbours.** For each of the 57,725 bases `α(p,q,r,s)` of `F_4` within three
  elementary Nielsen moves of the standard basis, the rose mapping torus in that basis is
  excluded by the same index-9 cover. In each case, the pushforward of `z` to `X_L` has two
  nonzero lifts of one 2-cell, or a coefficient of absolute value at least 2.

## Consequences for the lane

- A route to `ρ = 0` through the natural fibred `K(G,1)` is closed for the whole Nielsen ball of
  radius 3. The obstruction is one explicit cycle and one permutation representation. It is not a
  relation-module or character phenomenon, so it is independent of the w12/w13 obstructions.
- (T0) reduces "does this `X` realize `RP(H,G)`?" to the support of one canonical cycle. Every
  finite cover of `X` then gives a certificate. This is a uniform finite detector on the
  realization side: to kill a family of `K(G,1)`s it is enough to find one `L`.
- The brief's step (a uniform finite relation-gap detector for the slide route) remains open. The
  obvious `H_2` central-quotient detectors fail because the two `t`-exponent sums differ by `±1`.
  This lane turned instead to realizations inside fixed complexes.

## Next step

Decide (T4) for all marked roses. Find an `Aut(F_4)`-invariant form of "the pushforward of
`c_H ∈ H_1(N)` to `H_1(L ∩ F_4)` has a doubled letter", for example a norm on
`H_1(L ∩ F_4)` that is `≥ 2` on `c_L` in every basis. Then pass to non-rose marked graphs and to
the other fibrations of `G` in its BNS cone. A proof for all of them would leave only non-fibred
2-dimensional `K(G,1)`s as possible realizations of `RP(H,G)`.
