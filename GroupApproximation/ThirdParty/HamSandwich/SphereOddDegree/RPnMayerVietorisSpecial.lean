import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAffineOverlapSphere
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.MayerVietoris
import Mathlib

/-!
# Mayer–Vietoris specialization for the affine cover of `RP (n+1)`

This file packages the singular Mayer–Vietoris isomorphism for the specific
two-set open cover of `RP (n+1)` used in the inductive computation of its
mod-2 homology:

* `U = rpDeletedNorthOpen n` — the complement of the north point, homotopy
  equivalent to `RP n`;
* `V = rpAffineCellOpen n` — the affine cell, contractible.

The main public target is `rpMVHomologyIso_succ_to_sphere`, which combines the
raw Mayer–Vietoris connecting isomorphism with the identification of the overlap
`U ∩ V` with the sphere `Sⁿ`.  Together with the vanishing-transfer lemmas for
the two cover pieces, this is exactly the bridge required by the induction
(handled in a later prompt).
-/

open CategoryTheory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AffineBarycentricSubdivision

/-! ## Raw Mayer–Vietoris isomorphism -/

/-- The raw Mayer–Vietoris connecting isomorphism for the affine cover of
`RP (n+1)`: assuming the mod-2 homologies of `U = rpDeletedNorthOpen n` and
`V = rpAffineCellOpen n` vanish in degrees `j` and `j + 1`, the `(j+1)`-st
homology of `RP (n+1)` is isomorphic to the `j`-th homology of the overlap
`U ∩ V`. -/
noncomputable def rpMVHomologyIso_succ_raw
    (n j : Nat)
    (hU_succ : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpDeletedNorthOpen n : Set (rpAmbientSpace n))).homology (j + 1)))
    (hV_succ : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpAffineCellOpen n : Set (rpAmbientSpace n))).homology (j + 1)))
    (hU_j : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpDeletedNorthOpen n : Set (rpAmbientSpace n))).homology j))
    (hV_j : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpAffineCellOpen n : Set (rpAmbientSpace n))).homology j)) :
    homologyZMod2 (TopCat.of (RP (n + 1))) (j + 1)
      ≅ (subChainComplex (ZMod 2) (rpAmbientSpace n)
          ((rpDeletedNorthOpen n : Set (rpAmbientSpace n)) ∩
           (rpAffineCellOpen n : Set (rpAmbientSpace n)))).homology j := by
  change (singularChainComplex (ZMod 2) (rpAmbientSpace n)).homology (j + 1)
      ≅ _
  exact mvHomologyIso_succ
    (R := ZMod 2)
    (X := rpAmbientSpace n)
    (rpDeletedNorthOpen n)
    (rpAffineCellOpen n)
    (rpDeletedNorth_sup_rpAffineCellOpen n)
    j hU_succ hV_succ hU_j hV_j

/-! ## Composition with the overlap-sphere isomorphism -/

/-- The Mayer–Vietoris bridge in the form needed by the induction: assuming the
mod-2 homologies of the two cover pieces vanish in degrees `j` and `j + 1`, the
`(j+1)`-st homology of `RP (n+1)` is isomorphic to the `j`-th homology of the
sphere `Sⁿ`. -/
noncomputable def rpMVHomologyIso_succ_to_sphere
    (n j : Nat)
    (hU_succ : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpDeletedNorthOpen n : Set (rpAmbientSpace n))).homology (j + 1)))
    (hV_succ : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpAffineCellOpen n : Set (rpAmbientSpace n))).homology (j + 1)))
    (hU_j : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpDeletedNorthOpen n : Set (rpAmbientSpace n))).homology j))
    (hV_j : IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpAffineCellOpen n : Set (rpAmbientSpace n))).homology j)) :
    homologyZMod2 (TopCat.of (RP (n + 1))) (j + 1)
      ≅ homologyZMod2 (TopCat.of (Sphere n)) j :=
  rpMVHomologyIso_succ_raw n j hU_succ hV_succ hU_j hV_j ≪≫
    rpAffineOverlap_subspaceHomologyIso_sphere n j

/-! ## Vanishing-transfer lemmas for `U = rpDeletedNorthOpen n` -/

/-- If the mod-2 homology of `RP n` vanishes in degree `k`, then so does the
mod-2 subchain homology of the deleted-north open `U = rpDeletedNorthOpen n`. -/
theorem rpDeletedNorth_subspaceHomology_isZero_of_lower
    (n k : Nat)
    (h : IsZero (homologyZMod2 (TopCat.of (RP n)) k)) :
    IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpDeletedNorthOpen n : Set (rpAmbientSpace n))).homology k) :=
  IsZero.of_iso h (rpDeletedNorth_subspaceHomologyIso_lower n k)

/-! ## Vanishing-transfer lemma for `V = rpAffineCellOpen n`

The positive-degree vanishing of the affine cell's mod-2 subchain homology is
already provided by `rpAffineCell_subspaceHomology_isZero_pos` (from prompt 04),
re-exported here for convenience. -/

/-- The positive-degree mod-2 subchain homology of the affine cell
`V = rpAffineCellOpen n` vanishes. -/
theorem rpAffineCell_subspaceHomology_isZero_of_pos
    (n m : Nat) (hm : 1 ≤ m) :
    IsZero ((subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpAffineCellOpen n : Set (rpAmbientSpace n))).homology m) :=
  rpAffineCell_subspaceHomology_isZero_pos n m hm

/-! ## Convenience iso-to-zero lemma -/

/-- If `X ≅ Y` and `Y` is a zero object, then `X` is a zero object. -/
theorem isZero_of_iso_to_isZero {C : Type*} [Category C]
    {X Y : C} (e : X ≅ Y) (hY : IsZero Y) : IsZero X :=
  IsZero.of_iso hY e

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
