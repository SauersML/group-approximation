import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnDeletedNorthSphereDeformation
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyAboveDimension
import Mathlib

/-!
# The deleted-north projective chart retracts onto the lower projective space

This module descends the antipodal-equivariant deformation constructed on the
deleted-north sphere band and packages the resulting homotopy equivalence and
its mod-two homology isomorphism.
-/

noncomputable section

open CategoryTheory

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## The restricted quotient map upstairs -/

/-- The restricted quotient map `band → rpDeletedNorthSpace n`. -/
noncomputable def deletedNorthProj (n : Nat) :
    C(sphereDeletedNorthSet n, rpDeletedNorthSpace n) where
  toFun x := ⟨proj (n + 1) x.1, by
    show proj (n + 1) x.1 ∈ rpDeletedNorthSet n
    rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]; exact x.2⟩
  continuous_toFun := (proj_restrict_deletedNorth_isQuotientMap n).continuous

theorem deletedNorthProj_isQuotientMap (n : Nat) :
    Topology.IsQuotientMap (deletedNorthProj n) :=
  proj_restrict_deletedNorth_isQuotientMap n

@[simp]
theorem deletedNorthProj_coe (n : Nat) (x : sphereDeletedNorthSet n) :
    ((deletedNorthProj n x : rpDeletedNorthSpace n) : RP (n + 1)) = proj (n + 1) x.1 := rfl

/-! ## The map `rpDeletedNorthSpace n → RP n` -/

/-- The map `band → RP n`, `x ↦ proj n (deletedNorthBandToSphere n x)`. -/
noncomputable def rpDeletedNorthToLowerAux (n : Nat) :
    C(sphereDeletedNorthSet n, RP n) :=
  (proj n).comp (deletedNorthBandToSphere n)

theorem rpDeletedNorthToLower_factors (n : Nat) :
    Function.FactorsThrough (rpDeletedNorthToLowerAux n) (deletedNorthProj n) := by
  intro a b hab
  have hp : proj (n + 1) a.1 = proj (n + 1) b.1 := congrArg Subtype.val hab
  rcases eq_or_eq_neg_of_proj_eq hp with h | h
  · have hab' : a = b := Subtype.ext h
    rw [hab']
  · have ha : a = ⟨-b.1, by
        simpa using (sphereDeletedNorthSet_neg_iff n b.1).2 b.2⟩ := Subtype.ext h
    rw [ha]
    change proj n (deletedNorthBandToSphere n ⟨-b.1, _⟩) =
      proj n (deletedNorthBandToSphere n b)
    rw [deletedNorthBandToSphere_neg, proj_neg]

/-- The descended map `rpDeletedNorthSpace n → RP n`. -/
noncomputable def rpDeletedNorthToLower (n : Nat) : C(rpDeletedNorthSpace n, RP n) :=
  (deletedNorthProj_isQuotientMap n).lift (rpDeletedNorthToLowerAux n)
    (rpDeletedNorthToLower_factors n)

@[simp]
theorem rpDeletedNorthToLower_proj
    (n : Nat) (x : sphereDeletedNorthSet n) :
    rpDeletedNorthToLower n
      ⟨proj (n + 1) x.1, by
        show proj (n + 1) x.1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]; exact x.2⟩
      = proj n (deletedNorthBandToSphere n x) := by
  -- By definition of the quotient map, we have that the composition of the quotient map and the projection is equal to the projection.
  apply DFunLike.congr_fun (Topology.IsQuotientMap.lift_comp (deletedNorthProj_isQuotientMap n) (rpDeletedNorthToLowerAux n) (rpDeletedNorthToLower_factors n)) x

/-! ## The map `RP n → rpDeletedNorthSpace n` -/

theorem lowerToRpDeletedNorth_wd (n : Nat) (a b : Sphere n) (hab : a ≈ b) :
    (⟨proj (n + 1) (sphereToDeletedNorthBand n a).1, by
        show proj (n + 1) (sphereToDeletedNorthBand n a).1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
        exact (sphereToDeletedNorthBand n a).2⟩ : rpDeletedNorthSpace n)
      = ⟨proj (n + 1) (sphereToDeletedNorthBand n b).1, by
        show proj (n + 1) (sphereToDeletedNorthBand n b).1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
        exact (sphereToDeletedNorthBand n b).2⟩ := by
  cases' hab with h h;
  · aesop;
  · simp +decide [ h, sphereToDeletedNorthBand_neg ];
    exact Or.inr rfl

theorem continuous_lowerToRpDeletedNorth (n : Nat) :
    Continuous (fun y : Sphere n =>
      (⟨proj (n + 1) (sphereToDeletedNorthBand n y).1, by
        show proj (n + 1) (sphereToDeletedNorthBand n y).1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
        exact (sphereToDeletedNorthBand n y).2⟩ : rpDeletedNorthSpace n)) := by
  -- The composition of continuous functions is continuous.
  apply Continuous.subtype_mk;
  exact Continuous.comp (proj (n + 1)).continuous
    (continuous_subtype_val.comp (continuous_sphereToDeletedNorthBand n))

/-- The descended map `RP n → rpDeletedNorthSpace n`. -/
noncomputable def lowerToRpDeletedNorth (n : Nat) : C(RP n, rpDeletedNorthSpace n) where
  toFun := Quotient.lift
    (fun y : Sphere n => (⟨proj (n + 1) (sphereToDeletedNorthBand n y).1, by
        show proj (n + 1) (sphereToDeletedNorthBand n y).1 ∈ rpDeletedNorthSet n
        rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
        exact (sphereToDeletedNorthBand n y).2⟩ : rpDeletedNorthSpace n))
    (lowerToRpDeletedNorth_wd n)
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_lowerToRpDeletedNorth n

@[simp]
theorem lowerToRpDeletedNorth_proj (n : Nat) (y : Sphere n) :
    lowerToRpDeletedNorth n (proj n y)
      = ⟨proj (n + 1) (sphereToDeletedNorthBand n y).1, by
          show proj (n + 1) (sphereToDeletedNorthBand n y).1 ∈ rpDeletedNorthSet n
          rw [← Set.mem_preimage, preimage_rpDeletedNorthSet]
          exact (sphereToDeletedNorthBand n y).2⟩ :=
  rfl

/-! ## The right inverse is an equality -/

theorem rpDeletedNorth_right_inv_homotopic (n : Nat) :
    ContinuousMap.Homotopic
      ((rpDeletedNorthToLower n).comp (lowerToRpDeletedNorth n))
      (ContinuousMap.id (RP n)) := by
  have heq : (rpDeletedNorthToLower n).comp (lowerToRpDeletedNorth n) =
      ContinuousMap.id (RP n) := by
    apply RP.hom_ext
    intro y
    rw [ContinuousMap.comp_apply, lowerToRpDeletedNorth_proj,
      rpDeletedNorthToLower_proj]
    have hy := DFunLike.congr_fun
      (deletedNorthBandToSphere_comp_sphereToDeletedNorthBand n) y
    exact congrArg (proj n) hy
  rw [heq]


end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
