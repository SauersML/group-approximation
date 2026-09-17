---
rg: 2
id: eilenberg-ganea-conjecture
kind: claim
title: Every group of cohomological dimension 2 has a 2-dimensional Eilenberg--MacLane space
root: true
distinct_from:
  whitehead-asphericity-conjecture: that concerns subcomplexes of aspherical 2-complexes; this concerns the geometric dimension of groups of cohomological dimension 2.
  bestvina-brady-poincare-kernel-has-geometric-dimension-three: that is a specific counterexample statement, which refutes this conjecture if established.
refuted_by:
  - bestvina-brady-poincare-kernel-has-geometric-dimension-three
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**OPEN.** The Eilenberg--Ganea conjecture, in the form recalled by
Bestvina--Brady (Invent. Math. 129 (1997), p. 461, read from the Springer PDF
on MSI): "Recall that the Eilenberg-Ganea conjecture states that if a group H
has cohomological dimension 2, then it has a 2-dimensional Eilenberg-Mac Lane
space K(H,1)."

**Links.** `eilenberg-ganea-or-whitehead-is-false` (Bestvina--Brady
Theorem 8.7): this conjecture or `whitehead-asphericity-conjecture` is false.

## Attempts

1. **Bestvina--Brady kernels (2026-09-13).** The kernel `H_L` for a flag
   triangulation `L` of a spine of the Poincaré homology sphere has
   cohomological dimension 2. Geometric dimension 3 would refute this
   conjecture: `bestvina-brady-poincare-kernel-has-geometric-dimension-three`.
   Bestvina--Brady's closing remark (p. 470) conjectures that it does, through
   an unproved statement about ε-maps. Undecided.
2. **Cockcroft presentations over residually nilpotent augmentation ideals
   (2026-09-17).** `cockcroft-2-complexes-over-rn-cd-two-groups-are-aspherical`
   extends Gersten's finite asphericity criterion to 2-complexes of any size.
   Hypotheses: the fundamental group has cd ≤ 2 and ⋂ Iⁿ(ZG) = 0, which covers
   every subgroup of a right-angled Artin group.

   From it, `rn-cd-two-group-has-gd-two-iff-cockcroft-presentation` proves a
   two-directional reduction:
   - gd `H_L` = 2 iff `H_L` has a presentation F/N whose relators are Z-linearly
     independent in N/[F,N];
   - any such presentation has infinitely many generators.

   Consequently, Eilenberg--Ganea for residually torsion-free nilpotent cd-2 groups
   becomes a linear-independence problem for relators modulo [F,N], instead of the
   vanishing of a ZG-module. This does not decide `H_L`.

3. **Cardinality-minimal counterexample (2026-09-17, inverter).** The approach filters a cd-2 group by a continuous chain
   of subgroups (elementary submodels) and nests 2-dimensional `K(G_α,1)`'s as subcomplexes, taking unions at limits.
   - **Unconditional.** When every `G_α` is free, every 2-dimensional `K(G_α,1)` extends; the tool is a double mapping
     cylinder over a graph. So every continuous union of free groups has `gd ≤ 2`. This includes all `ℵ_1`-free groups of
     size `ℵ_1` and all `κ`-free groups of size `κ`: `continuous-free-chain-unions-have-gd-two`.
   - **Conditional.** Every elementary-submodel step satisfies `pd I_{G_β/G_α} ≤ 1`. So the relative countable statement
     REG_ω (extend an *arbitrary* 2-dimensional `K(H,1)`) gives EG for all groups of size `≤ ℵ_1`:
     `relative-countable-eg-gives-eg-for-aleph-one-groups`.
     - **Consequence for counterexamples.** A counterexample of minimal size `ℵ_1` forces a countable pair with a
       non-free base failing REG_ω.
   - **Where it stops.** REG_ω contains countable EG, and for a presentation relative to `K` its `π_2` is projective. So
     it meets the same Eilenberg--Ganea obstruction, and the reduction does not simplify the countable problem.
     - Geometric obstructions to extension, such as a PD²-subgroup with larger commensurator, are already detected by
       the pd condition: restriction to `H` must surject `H^2(H,M)` onto `∏ H^2(H ∩ gHg^{-1},M)`.
   - **Dead: pro-p and prounipotent Whitehead analogs** (Mikhovich, arXiv:2105.00281). For acyclic `L`, `π_1(L)` is
     perfect, so these completions are trivial. They cannot see `gd H_L`.
   - **Dead: slicing `K` to lift REG_ω to `ℵ_1`-sized pairs** (relaunch, 2026-09-17). Filter an `ℵ_1`-sized pair
     `H ≤ G` by elementary submodels and set `K_α = K ∩ M_α` (aspherical, with `π_1 = H_α`, by elementarity of
     van Kampen diagrams). The successor step must extend `Z = X_α ∪_{K_α} K_{α+1}`, whose `π_1` is
     `G_α *_{H_α} H_{α+1}`, and this group need not inject into `G_{α+1}`.
     - **Example.** `G = Z × F(ℵ_1)`, `H = F(ℵ_1)`, `pd I_{G/H} = cd F = 1`. The commutator of `t` with any
       `y ∈ H_{α+1} ∖ H_α` is reduced in the amalgam but trivial in `G`. Extension is still possible here
       (`continuous-free-chain-unions-have-gd-two`, Lemma 1), so the failure is in the method, not the statement.
     - So the `ℵ_2` step needs a countable *square* relative statement for subcomplexes that are not
       `π_1`-injective, which REG_ω does not supply.
   - **Converse: REG_ω ⇔ EG up to `ℵ_1`** (w3-048, 2026-09-17). `aleph-one-eg-is-equivalent-to-relative-countable-eg`.
     - **Swap: yes.** Extending a 2-dimensional `K(H,1)` depends only on the pair. Given `K' ⊆ X'` and any `K ≃ K'`,
       the adjunction `X' ∪_g K` along a homotopy equivalence is a 2-dimensional `K(G,1)` containing `K`.
     - **Engine.** For countable `H ≤ G`, some aspherical 2-complex pair realizes `H ≤ G` iff
       `gd ⁎_H^{ω_1} G ≤ 2`. Slice a 2-dimensional `K(Γ_{ℵ_1},1)` by a countable elementary submodel, which gives a
       `π_1`-injective subcomplex carrying `Γ_δ`. Then pass to the cover for the copy `G_δ`, where
       `Γ_δ ∩ G_δ = H`: `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two`.
     - **Consequence.** An `ℵ_1`-sized counterexample can be taken to be `⁎_H^{ω_1} G` for one countable pair with
       non-free `H`. Whether countable EG implies EG at `ℵ_1` is the same as whether `gd ≤ 2` passes from
       `⁎_H^{ω} G` to `⁎_H^{ω_1} G`, and remains open. This is a `Π^1_2` statement (sketch), so forcing cannot
       settle it.
