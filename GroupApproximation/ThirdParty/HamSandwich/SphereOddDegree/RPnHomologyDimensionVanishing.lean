import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnMayerVietorisSpecial
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnLowDimensional
import GroupApproximation.Meta.AxiomGuard
import Mathlib

/-!
# Above-dimension vanishing of the mod-2 homology of `RPⁿ`

This file proves, by induction on `n` using the Mayer–Vietoris bridge packaged
in `RPnMayerVietorisSpecial.lean`, that the mod-2 singular homology of real
projective space `RPⁿ` vanishes in all degrees `k > n`:

* `rpHomologyZMod2_isZero_above_dim` — the main statement `H_k(RPⁿ; F₂) = 0` for
  `n < k`.

The base case `RP⁰` is handled by `rpHomologyZMod2_zero_isZero_pos`, using that
`RP⁰` is totally disconnected (it is a point).
-/

open CategoryTheory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- **Base case.** For `0 < k`, the mod-2 homology of `RP⁰` vanishes.  Since
`RP⁰` is a point (a `Subsingleton`, hence totally disconnected), its mod-2
singular homology vanishes in positive degrees. -/
theorem rpHomologyZMod2_zero_isZero_pos
    (k : Nat) (hk : 0 < k) :
    IsZero (homologyZMod2 (TopCat.of (RP 0)) k) := by
  have hzero :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat (ZMod 2)) k
      (ModuleCat.of (ZMod 2) (ZMod 2))
      (TopCat.of (RP 0)) hk.ne'
  change IsZero (homologyZMod2 (TopCat.of (RP 0)) k) at hzero
  exact hzero

/-- **Above-dimension vanishing for `RPⁿ`.** For `n < k`, `H_k(RPⁿ; F₂) = 0`. -/
theorem rpHomologyZMod2_isZero_above_dim
    (n k : Nat) (hk : n < k) :
    IsZero (homologyZMod2 (TopCat.of (RP n)) k) := by
  induction n generalizing k with
  | zero =>
      exact rpHomologyZMod2_zero_isZero_pos k hk
  | succ n ih =>
      obtain ⟨j, hj_eq⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      subst hj_eq
      have hj_gt_n : n < j := by omega
      have hj_pos : 1 ≤ j := by omega
      have hU_succ : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
          (rpDeletedNorthOpen n : Set (rpAmbientSpace n))).homology (j + 1)) := by
        apply rpDeletedNorth_subspaceHomology_isZero_of_lower
        exact ih (j + 1) (by omega)
      have hU_j : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
          (rpDeletedNorthOpen n : Set (rpAmbientSpace n))).homology j) := by
        apply rpDeletedNorth_subspaceHomology_isZero_of_lower
        exact ih j hj_gt_n
      have hV_succ : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
          (rpAffineCellOpen n : Set (rpAmbientSpace n))).homology (j + 1)) := by
        exact rpAffineCell_subspaceHomology_isZero_pos n (j + 1) (by omega)
      have hV_j : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
          (rpAffineCellOpen n : Set (rpAmbientSpace n))).homology j) := by
        exact rpAffineCell_subspaceHomology_isZero_pos n j hj_pos
      have hSphere : IsZero (homologyZMod2 (TopCat.of (Sphere n)) j) :=
        sphereModTwoHomology_isZero_of_gt n j hj_gt_n
      exact IsZero.of_iso hSphere
        (rpMVHomologyIso_succ_to_sphere n j hU_succ hV_succ hU_j hV_j)

/-- Convenience specialization: `H_{n+1}(RPⁿ; F₂) = 0`. -/
theorem rpHomologyZMod2_topPlusOne_isZero (n : Nat) :
    IsZero (homologyZMod2 (TopCat.of (RP n)) (n + 1)) :=
  rpHomologyZMod2_isZero_above_dim n (n + 1) (Nat.lt_succ_self n)

/-- Closed audit endpoint for RP dimension vanishing in mod-two homology. -/
theorem rpHomology_dimension_vanishing_closed :
    (∀ n k : Nat, n < k →
      IsZero (homologyZMod2 (TopCat.of (RP n)) k)) ∧
    (∀ n : Nat,
      IsZero (homologyZMod2 (TopCat.of (RP n)) (n + 1))) :=
  ⟨rpHomologyZMod2_isZero_above_dim, rpHomologyZMod2_topPlusOne_isZero⟩

#audit_closed_axioms rpHomology_dimension_vanishing_closed

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
