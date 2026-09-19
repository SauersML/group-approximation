import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnDeletedNorthProjectiveMaps
import GroupApproximation.Meta.AxiomGuard
import Mathlib

/-!
# The descended deleted-north deformation and homology isomorphism
-/

noncomputable section

open CategoryTheory

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## The descended homotopy for the left inverse -/

/-
The key fiberwise compatibility: the upstairs homotopy descends.
-/
theorem deletedNorthProj_homotopy_compat
    (n : Nat) (t : unitInterval) {x x' : sphereDeletedNorthSet n}
    (h : deletedNorthProj n x = deletedNorthProj n x') :
    deletedNorthProj n (deletedNorthBandHomotopy n (t, x))
      = deletedNorthProj n (deletedNorthBandHomotopy n (t, x')) := by
  have hp : proj (n + 1) x.1 = proj (n + 1) x'.1 :=
    congrArg Subtype.val h
  rcases eq_or_eq_neg_of_proj_eq hp with h_eq | h_neg
  · have hxx' : x = x' := Subtype.ext h_eq
    rw [hxx']
  · have hx : x = ⟨-x'.1, by
        simpa using (sphereDeletedNorthSet_neg_iff n x'.1).2 x'.2⟩ :=
      Subtype.ext h_neg
    rw [hx, deletedNorthBandHomotopy_neg]
    apply Subtype.ext
    exact proj_neg (deletedNorthBandHomotopy n (t, x')).1

/-- The descended homotopy value function. -/
noncomputable def deletedNorthRPHomotopyFun
    (n : Nat) (p : unitInterval × rpDeletedNorthSpace n) : rpDeletedNorthSpace n :=
  deletedNorthProj n
    (deletedNorthBandHomotopy n
      (p.1, Function.surjInv (deletedNorthProj_isQuotientMap n).surjective p.2))

theorem deletedNorthRPHomotopyFun_proj
    (n : Nat) (t : unitInterval) (x : sphereDeletedNorthSet n) :
    deletedNorthRPHomotopyFun n (t, deletedNorthProj n x)
      = deletedNorthProj n (deletedNorthBandHomotopy n (t, x)) := by
  unfold deletedNorthRPHomotopyFun
  apply deletedNorthProj_homotopy_compat
  exact Function.surjInv_eq (deletedNorthProj_isQuotientMap n).surjective _

theorem continuous_deletedNorthRPHomotopyFun (n : Nat) :
    Continuous (deletedNorthRPHomotopyFun n) := by
  apply (deletedNorthProj_isQuotientMap n).continuous_lift_prod_right
  have hfun : (fun p : unitInterval × sphereDeletedNorthSet n =>
      deletedNorthRPHomotopyFun n (p.1, deletedNorthProj n p.2))
      = fun p => deletedNorthProj n (deletedNorthBandHomotopy n p) := by
    funext p
    exact deletedNorthRPHomotopyFun_proj n p.1 p.2
  rw [hfun]
  exact (deletedNorthProj n).continuous.comp (deletedNorthBandHomotopy n).continuous

theorem deletedNorthRPHomotopy_zero (n : Nat) (q : rpDeletedNorthSpace n) :
    deletedNorthRPHomotopyFun n (0, q)
      = (lowerToRpDeletedNorth n).comp (rpDeletedNorthToLower n) q := by
  obtain ⟨x, rfl⟩ := (deletedNorthProj_isQuotientMap n).surjective q
  have hlower : rpDeletedNorthToLower n (deletedNorthProj n x) =
      proj n (deletedNorthBandToSphere n x) :=
    rpDeletedNorthToLower_proj n x
  rw [deletedNorthRPHomotopyFun_proj, ContinuousMap.comp_apply, hlower,
    lowerToRpDeletedNorth_proj]
  exact congrArg (deletedNorthProj n) (deletedNorthBandHomotopy_zero n x)

theorem deletedNorthRPHomotopy_one (n : Nat) (q : rpDeletedNorthSpace n) :
    deletedNorthRPHomotopyFun n (1, q) = ContinuousMap.id _ q := by
  obtain ⟨x, hx⟩ := ( deletedNorthProj_isQuotientMap n ).surjective q;
  rw [ ← hx, deletedNorthRPHomotopyFun_proj ];
  exact congr_arg _ ( deletedNorthBandHomotopy_one n x )

/-- The descended homotopy `(lowerToRpDeletedNorth ∘ rpDeletedNorthToLower) ≃ id`. -/
noncomputable def deletedNorthRPHomotopy (n : Nat) :
    ContinuousMap.Homotopy
      ((lowerToRpDeletedNorth n).comp (rpDeletedNorthToLower n))
      (ContinuousMap.id (rpDeletedNorthSpace n)) where
  toFun := deletedNorthRPHomotopyFun n
  continuous_toFun := continuous_deletedNorthRPHomotopyFun n
  map_zero_left := deletedNorthRPHomotopy_zero n
  map_one_left := deletedNorthRPHomotopy_one n

theorem rpDeletedNorth_left_inv_homotopic (n : Nat) :
    ContinuousMap.Homotopic
      ((lowerToRpDeletedNorth n).comp (rpDeletedNorthToLower n))
      (ContinuousMap.id (rpDeletedNorthSpace n)) :=
  ⟨deletedNorthRPHomotopy n⟩

/-! ## The final homotopy equivalence -/

/-- The deleted-north chart deformation retracts onto `RP n`. -/
noncomputable def rpDeletedNorth_homotopyEquiv_lower (n : Nat) :
    ContinuousMap.HomotopyEquiv (rpDeletedNorthSpace n) (RP n) where
  toFun := rpDeletedNorthToLower n
  invFun := lowerToRpDeletedNorth n
  left_inv := rpDeletedNorth_left_inv_homotopic n
  right_inv := rpDeletedNorth_right_inv_homotopic n

/-! ## Homology corollaries -/

/-- The mod-2 homology of the deleted-north chart agrees with that of `RP n`. -/
noncomputable def rpDeletedNorth_homologyIso_lower (n k : Nat) :
    homologyZMod2 (TopCat.of (rpDeletedNorthSpace n)) k
      ≅ homologyZMod2 (TopCat.of (RP n)) k :=
  homologyIsoOfHomotopyEquivModule
    (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) k
    (rpDeletedNorth_homotopyEquiv_lower n)

/-- Subchain-homology form of the previous isomorphism. -/
noncomputable def rpDeletedNorth_subspaceHomologyIso_lower (n k : Nat) :
    (subChainComplex (ZMod 2) (rpAmbientSpace n)
      (rpDeletedNorthOpen n : Set (rpAmbientSpace n))).homology k
      ≅ homologyZMod2 (TopCat.of (RP n)) k :=
  subspaceHomologyIso _ k ≪≫ rpDeletedNorth_homologyIso_lower n k

/-- Closed audit endpoint for the deleted-north homology equivalence. -/
theorem rpDeletedNorth_homology_iso_closed :
    Nonempty (∀ n k : Nat,
      homologyZMod2 (TopCat.of (rpDeletedNorthSpace n)) k
        ≅ homologyZMod2 (TopCat.of (RP n)) k) :=
  ⟨rpDeletedNorth_homologyIso_lower⟩

#audit_closed_axioms rpDeletedNorth_homology_iso_closed

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
