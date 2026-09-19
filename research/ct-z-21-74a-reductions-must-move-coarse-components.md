---
rg: 2
id: ct-z-21-74a-reductions-must-move-coarse-components
kind: claim
title: "Kourovka 21.74(a) sees only coarse structure: whether g permutes a residue partition depends only on the action of g on the clopen sets fixed by some power of g; machine (FRACTRAN, counter) encodings change only thin sets, and positive-ray elements have computable coarse structure, so an undecidability reduction needs a rank-two family whose invariant clopen structure itself depends on halting"
distinct_from:
  ct-z-residue-partitions-cannot-carve-thin-invariant-sets: that proves thin invariant sets cannot contain a co-class; this states the general principle behind it, and says what any reduction must do instead.
  ct-p-z-positive-ray-kourovka-21-74a-is-decidable: that decides the positive ray; this records why the known undecidability techniques cannot reach the rest.
---

**ESTABLISHED** for the principle and its corollaries (lane proof, elementary, not reviewed).
Kourovka 21.74(a) (S. Kohl) stays **OPEN** beyond the positive ray. This is a barrier result,
not a solution.

## Principle (coarse action)

For `g ∈ CT(Z)`, let `𝒞(g)` be the set of clopen `W ⊆ Ẑ` with `ĝ^k(W) = W` for some `k ≥ 1`.
- **Claim.** If `g, g′ ∈ CT(Z)` have `𝒞(g) ⊆ 𝒞(g′)` and `ĝ(W) = ĝ′(W)` for all `W ∈ 𝒞(g)`, then
  YES(`g`) implies YES(`g′`). So YES is a function of the pair `(𝒞(g), ĝ|_(𝒞(g)))`, the *coarse
  action*.
- **Proof.** Let `g` permute the box partition `𝒫`. Every part is in `𝒞(g)`, because
  `ĝ^(|𝒫|!)` fixes it. So `ĝ′(C) = ĝ(C) ∈ 𝒫` for every part `C`. ∎

## Corollaries (the three known routes, and why they stop)

1. **Machine encodings touch only thin sets.**
   - Counter-machine and FRACTRAN-type elements are multiplicative, i.e. valuation-coded, as in
     `ct-z-finite-cycle-problems-are-undecidable` and `ct-z-conjugacy-problem-is-undecidable`.
     The sets their computations create lie in valuation strata inside `pZ`.
   - Next to an indecomposable mixer, such sets never enter a YES partition, since they contain no
     co-class (`ct-z-residue-partitions-cannot-carve-thin-invariant-sets`). So halting does not
     change the coarse action.
2. **The positive ray is computable.** For slopes in `γ^Z` (`γ` an integer), `𝒞(g)` is generated
   by finitely many computable flow components with computable hulls, a finite-order part, and
   holonomy-bounded fibres (`ct-p-z-positive-ray-kourovka-21-74a-is-decidable`).
3. **Brin–Thompson codings do not transplant.** Belk–Bleak's undecidability in `2V` rests on
   independent prefix writes on two coordinates, which CT(Z) cannot supply
   (`ct-z-torsion-problem-and-the-brin-thompson-transplant`, Theorem 2).

## What a reduction would need

- **The requirement.** A computable family `g_M` whose coarse action changes with halting, e.g.
  two attractor basins whose clopen hulls merge iff `M` halts. By Corollary 2 it must have
  mixed-sign or rank-two slopes.
- **The 2V analogue.** Belk–Bleak's Theorem 6.8 (`2V` has an attracting fixed point whose basin
  meets the dyadic points in a non-computable set, recorded in the torsion-problem node) is the
  model.
- **The gap.** No such element is known in CT(Z). Rank-two elements supply hyperbolic bases (a
  full shift through Conway's amusical permutation, and Collatz components), but no known
  construction makes a basin's clopen structure depend on a computation.

## Lesson for general BH

**YES certificates are coarse; machine encodings touch only thin sets.**
- Box-level (coordinate) questions about an element see only its clopen invariant structure.
- Computation embedded multiplicatively lives in thin strata, which that structure cannot see.
- So the undecidable dynamics that CT(Z) supports (finite cycles, conjugacy) is invisible to
  partition questions.
- Making a coordinate question hard requires machines that move *clopen* mass: arithmetic
  analogues of prefix writes, which the carry rule forbids on any one coordinate.
