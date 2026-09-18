import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnital
import GroupApproximation.KTheory.K1Scalar

/-!
# K-theory of non-unital C⋆-algebras: the zero map and the standard picture

Lane `TWWSch3d3a`, work order `WO-TWWSchafhauser-3d3-1`, for
`thm:fixed-radical-membership` (`non_mf_group_notes.tex`, l.1376--1378). The source is
M. Rørdam, F. Larsen, N. Laustsen, *An introduction to K-theory for C⋆-algebras*, §4.1--4.2
and §8.1.

* `unitHom J : ℂ → J⁺` is the unit map, and `scalarProj J = unitHom J ∘ scalarHom J : J⁺ → J⁺` is
  the scalar projection `x ↦ x.fst • 1`;
* `starMap_zero`: the unitized zero map `J⁺ → J'⁺` factors through `ℂ`;
* `KZeroN.map_zero_hom`, `KOneN.map_zero_hom`: the zero homomorphism induces zero on `K₀` and `K₁`.
  For `K₁`, this uses `K₁(ℂ) = 0` (`kOne_complex_eq_one`);
* `KZeroN.ofCycle x = [p] - [s(p)]` is the standard-picture element of `K₀(J)` attached to a
  projection `p` over `J⁺` (RLL Proposition 4.2.2), with its naturality `KZeroN.map_ofCycle`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

section Scalar

variable {J J' : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra J']

variable (J) in
/-- The unit map `ℂ → J⁺`. -/
def unitHom : ℂ →⋆ₐ[ℂ] Unitization ℂ J :=
  StarAlgHom.ofId ℂ (Unitization ℂ J)

theorem unitHom_apply (r : ℂ) : unitHom J r = algebraMap ℂ (Unitization ℂ J) r :=
  rfl

theorem scalarHom_unitHom (r : ℂ) : scalarHom J (unitHom J r) = r := by
  rw [scalarHom_apply]
  exact Unitization.fst_inl J r

variable (J) in
/-- The scalar projection `J⁺ → J⁺`, `x ↦ x.fst • 1` (RLL §4.1). -/
def scalarProj : Unitization ℂ J →⋆ₐ[ℂ] Unitization ℂ J :=
  (unitHom J).comp (scalarHom J)

theorem scalarProj_apply (x : Unitization ℂ J) :
    scalarProj J x = algebraMap ℂ (Unitization ℂ J) (scalarHom J x) :=
  rfl

theorem scalarHom_scalarProj (x : Unitization ℂ J) : scalarHom J (scalarProj J x) = scalarHom J x :=
  scalarHom_unitHom (J := J) (scalarHom J x)

/-- The unitization of the zero map factors through the scalars. -/
theorem starMap_zero :
    Unitization.starMap (0 : J →⋆ₙₐ[ℂ] J') = (unitHom J').comp (scalarHom J) := by
  refine StarAlgHom.ext fun x => ?_
  show algebraMap ℂ (Unitization ℂ J') x.fst + ((0 : J →⋆ₙₐ[ℂ] J') x.snd : Unitization ℂ J') =
    algebraMap ℂ (Unitization ℂ J') (scalarHom J x)
  rw [NonUnitalStarAlgHom.zero_apply, Unitization.inr_zero, add_zero, scalarHom_apply]

/-- The unitized maps commute with the scalar projections. -/
theorem starMap_scalarProj (φ : J →⋆ₙₐ[ℂ] J') (x : Unitization ℂ J) :
    Unitization.starMap φ (scalarProj J x) = scalarProj J' (Unitization.starMap φ x) := by
  show Unitization.starMap φ (algebraMap ℂ (Unitization ℂ J) (scalarHom J x)) =
    algebraMap ℂ (Unitization ℂ J') (scalarHom J' (Unitization.starMap φ x))
  rw [scalarHom_starMap]
  exact AlgHomClass.commutes (Unitization.starMap φ) (scalarHom J x)

end Scalar

/-! ### `K₀` -/

section KZero

variable {J J' : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra J']

/-- The zero homomorphism induces the zero map on `K₀`. -/
theorem KZeroN.map_zero_hom : KZeroN.map (0 : J →⋆ₙₐ[ℂ] J') = 0 := by
  have h : starRingHomOf (Unitization.starMap (0 : J →⋆ₙₐ[ℂ] J')) =
      (starRingHomOf (unitHom J')).comp (starRingHomOf (scalarHom J)) :=
    NonUnitalStarRingHom.ext fun y => DFunLike.congr_fun (starMap_zero (J := J) (J' := J')) y
  refine AddMonoidHom.ext fun x => Subtype.ext ?_
  have hx : KTheory.KZero.map (starRingHomOf (scalarHom J)) x.1 = 0 :=
    AddMonoidHom.mem_ker.mp x.2
  show KTheory.KZero.map (starRingHomOf (Unitization.starMap (0 : J →⋆ₙₐ[ℂ] J'))) x.1 = 0
  calc KTheory.KZero.map (starRingHomOf (Unitization.starMap (0 : J →⋆ₙₐ[ℂ] J'))) x.1
      = KTheory.KZero.map ((starRingHomOf (unitHom J')).comp
          (starRingHomOf (scalarHom J))) x.1 := by
        rw [h]
    _ = KTheory.KZero.map (starRingHomOf (unitHom J'))
          (KTheory.KZero.map (starRingHomOf (scalarHom J)) x.1) :=
        DFunLike.congr_fun (KTheory.KZero.map_comp (starRingHomOf (unitHom J'))
          (starRingHomOf (scalarHom J))) x.1
    _ = 0 := by rw [hx, map_zero]

theorem KZeroN.ofCycle_mem (x : KTheory.Cycle (Unitization ℂ J)) :
    KTheory.KZero.mk x - KTheory.KZero.mk (x.map (starRingHomOf (scalarProj J))) ∈
      AddMonoidHom.ker (KTheory.KZero.map (starRingHomOf (scalarHom J))) := by
  have h : (starRingHomOf (scalarHom J)).comp (starRingHomOf (scalarProj J)) =
      starRingHomOf (scalarHom J) :=
    NonUnitalStarRingHom.ext fun y => scalarHom_scalarProj y
  rw [AddMonoidHom.mem_ker, map_sub, KTheory.KZero.map_mk, KTheory.KZero.map_mk,
    ← KTheory.Cycle.map_comp, h, sub_self]

/-- **The standard picture of `K₀(J)`** (RLL Proposition 4.2.2). A projection `p` over `J⁺`
defines `[p] - [s(p)] ∈ K₀(J)`, where `s` is the scalar projection. -/
def KZeroN.ofCycle (x : KTheory.Cycle (Unitization ℂ J)) : KZeroN J :=
  ⟨KTheory.KZero.mk x - KTheory.KZero.mk (x.map (starRingHomOf (scalarProj J))),
    KZeroN.ofCycle_mem x⟩

theorem KZeroN.incl_ofCycle (x : KTheory.Cycle (Unitization ℂ J)) :
    KZeroN.incl (KZeroN.ofCycle x) =
      KTheory.KZero.mk x - KTheory.KZero.mk (x.map (starRingHomOf (scalarProj J))) :=
  rfl

/-- Naturality of the standard picture. -/
theorem KZeroN.map_ofCycle (φ : J →⋆ₙₐ[ℂ] J') (x : KTheory.Cycle (Unitization ℂ J)) :
    KZeroN.map φ (KZeroN.ofCycle x) =
      KZeroN.ofCycle (x.map (starRingHomOf (Unitization.starMap φ))) := by
  have h : (starRingHomOf (Unitization.starMap φ)).comp (starRingHomOf (scalarProj J)) =
      (starRingHomOf (scalarProj J')).comp (starRingHomOf (Unitization.starMap φ)) :=
    NonUnitalStarRingHom.ext fun y => starMap_scalarProj φ y
  refine Subtype.ext ?_
  show KTheory.KZero.map (starRingHomOf (Unitization.starMap φ))
      (KTheory.KZero.mk x - KTheory.KZero.mk (x.map (starRingHomOf (scalarProj J)))) =
    KTheory.KZero.mk (x.map (starRingHomOf (Unitization.starMap φ))) -
      KTheory.KZero.mk ((x.map (starRingHomOf (Unitization.starMap φ))).map
        (starRingHomOf (scalarProj J')))
  rw [map_sub, KTheory.KZero.map_mk, KTheory.KZero.map_mk,
    ← KTheory.Cycle.map_comp (starRingHomOf (Unitization.starMap φ))
      (starRingHomOf (scalarProj J)) x,
    ← KTheory.Cycle.map_comp (starRingHomOf (scalarProj J'))
      (starRingHomOf (Unitization.starMap φ)) x, h]

end KZero

/-! ### `K₁` -/

section KOne

attribute [local instance] unitizationOrder unitizationStarOrderedRing

variable {J J' : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra J']

/-- The zero homomorphism induces the zero map on `K₁`, because it factors through
`K₁(ℂ) = 0`. -/
theorem KOneN.map_zero_hom : KOneN.map (0 : J →⋆ₙₐ[ℂ] J') = 0 := by
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  haveI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  have h : KOne.map (Unitization.starMap (0 : J →⋆ₙₐ[ℂ] J')) =
      (KOne.map (unitHom J')).comp (KOne.map (scalarHom J)) := by
    rw [starMap_zero]
    exact KOne.map_comp _ _
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := (KOneN.ofMul (J := J)).surjective x
  have ha : KOne.map (scalarHom J) a = 1 := kOne_complex_eq_one _
  show KOneN.ofMul (KOne.map (Unitization.starMap (0 : J →⋆ₙₐ[ℂ] J')) a) =
    KOneN.ofMul (1 : KOne (Unitization ℂ J'))
  rw [h, MonoidHom.comp_apply, ha, map_one]

end KOne

end

end TWWSchafhauser
end Full
end GroupApproximation
