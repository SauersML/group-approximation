---
rg: 2
id: hyperbolic-3-manifold-groups-paunescu-class-proof
kind: route
title: Virtually fiber, put the surface-by-cyclic cover in the class by Folner induction, and move to finite-index overgroups and other lattices
target: hyperbolic-3-manifold-groups-in-paunescu-class
requires:
  - paunescu-class-closed-under-amenable-extensions
  - fpbs-fibered-3-manifold-cost-inputs
  - paunescu-sofic-action-class-permanence
  - sofic-action-class-closed-under-commensurability
  - paunescu-class-is-measure-equivalence-invariant
artifacts:
  - research/artifacts/paunescu-class-amenable-extensions-2026-09-12.md
---

# Proof

Artifact Section 2, Corollary 2.2.

1. **Surface groups.** For `g >= 2`, cutting a closed orientable surface along a separating simple
   closed curve splits it into surfaces of genus `h` and `g − h` with one boundary circle, whose
   fundamental groups are free of ranks `2h` and `2(g−h)`. So
   `π_1(S_g) = F_(2h) *_Z F_(2(g−h))`. Free groups are in `𝒮` (Păunescu Corollary 3.7) and `𝒮` is
   closed under amalgamation over amenable subgroups (Theorem 3.9), both in
   `paunescu-sofic-action-class-permanence`. So `π_1(S_g) ∈ 𝒮`.
2. **Fibered covers.** A closed hyperbolic 3-manifold `M` has a finite cover `M'` fibering over the
   circle with fiber a closed surface of genus at least two (`fpbs-fibered-3-manifold-cost-inputs`,
   Agol). The long exact sequence of the fibration gives `π_1(M') = π_1(S_g) ⋊ Z`. By
   `paunescu-class-closed-under-amenable-extensions` with `N = π_1(S_g)` and quotient `Z`,
   `π_1(M') ∈ 𝒮`.
3. **Finite-index overgroups.** `π_1(M')` has finite index in `π_1(M)`, so `π_1(M) ∈ 𝒮`
   (`sofic-action-class-closed-under-commensurability`, part 2).
4. **All lattices.** A cocompact lattice `Λ <= PSL_2(C)` has a torsion-free finite-index subgroup
   (Selberg's lemma, `Λ` being finitely generated and linear), which is `π_1` of a closed
   hyperbolic 3-manifold; so `Λ ∈ 𝒮` by step 3. Any lattice of `PSL_2(C)` is measure equivalent to a
   cocompact one (both are lattices of the same lcsc group, coupled by Haar measure), so it lies in
   `𝒮` by `paunescu-class-is-measure-equivalence-invariant`, as does every group measure equivalent
   to it.
