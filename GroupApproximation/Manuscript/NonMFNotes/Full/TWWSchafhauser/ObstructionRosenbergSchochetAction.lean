-- DRAFT (TWWSch3d3-3A). Imports/names of WO-3d3-3A-A..E are the ones requested from main;
-- retarget when they land. Not compiled.
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetActionAssembly
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetActionPiNatural
-- import <WO-A: BusbyCycle.isSemisplit_of_nuclear>
-- import <WO-B: ExtSS.comap_eq_of_nHomotopic>
-- import <WO-C: ExtSS.comap_stabCorner_bijective>
-- import <WO-D: ExtSS.comap_qalgPi_bijective>
-- import <WO-E: TWWKK.stabQ, TWWKK.kasparovKK, corner naturality, SeparableSpace instances>

/-!
# The Kasparov-product action on `Ext(-, J)`

`thm:fixed-radical-membership` (non_mf_group_notes.tex l.1376--1378).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.KK

variable (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [TopologicalSpace.SeparableSpace J]

/-- The Cuntz-picture data for `kasparovKK`: `A ←π— qA —corner→ 𝒦 ⊗ qA`. -/
noncomputable def ExtGroup.kasparovCuntzData :
    ExtSSCuntzData TWWKK.stabQ
      (fun A : SepCStarAlgebra.{0} => GroupApproximation.CStarExactness.IsNuclearCStarAlgebra A)
      J where
  M A := TWWKK.Qalg A
  mapM φ := TWWKK.Qalg.map (φ : _ →⋆ₙₐ[ℂ] _)
  p A := TWWKK.Qalg.pi A
  c A := TWWKK.Stab.corner (TWWKK.Qalg A)
  p_natural φ := qalg_pi_natural (φ : _ →⋆ₙₐ[ℂ] _)
  c_natural φ := TWWKK.stabQ_map_comp_corner φ
  semisplit hA x := BusbyCycle.isSemisplit_of_nuclear hA x
  p_bijective A := ExtSS.comap_qalgPi_bijective A
  c_bijective A := ExtSS.comap_stabCorner_bijective (TWWKK.Qalg A)
  homotopy h := ExtSS.comap_eq_of_nHomotopic h

/-- The left leg of `kasparovCuntzData` is Cuntz's projection `π_A : qA → A`. -/
theorem ExtGroup.kasparovCuntzData_p (A : SepCStarAlgebra.{0}) :
    (ExtGroup.kasparovCuntzData J).p A = TWWKK.Qalg.pi A :=
  rfl

/-- The right leg of `kasparovCuntzData` is the corner `qA → 𝒦 ⊗ qA`. -/
theorem ExtGroup.kasparovCuntzData_c (A : SepCStarAlgebra.{0}) :
    (ExtGroup.kasparovCuntzData J).c A = TWWKK.Stab.corner (TWWKK.Qalg A) :=
  rfl

/-- **The action of `kasparovKK` on `Ext(-, J)`** on nuclear objects. -/
noncomputable def ExtGroup.kasparovKKAction :
    ExtKKAction TWWKK.kasparovKK
      (fun A : SepCStarAlgebra.{0} => GroupApproximation.CStarExactness.IsNuclearCStarAlgebra A)
      J :=
  (ExtGroup.kasparovCuntzData J).toExtKKAction

/-- `kasparovKKAction` is the action assembled from `kasparovCuntzData`
(`TWWKK.kasparovKK` is `TWWKK.stabQ.toKasparovTheory` by definition). -/
theorem ExtGroup.kasparovKKAction_eq :
    ExtGroup.kasparovKKAction J = (ExtGroup.kasparovCuntzData J).toExtKKAction :=
  rfl

theorem ExtGroup.kasparovKKAction_classOf {A B : SepCStarAlgebra.{0}}
    (hA : GroupApproximation.CStarExactness.IsNuclearCStarAlgebra A)
    (hB : GroupApproximation.CStarExactness.IsNuclearCStarAlgebra B) (φ : A →⋆ₐ[ℂ] B) :
    (ExtGroup.kasparovKKAction J).act hA hB (TWWKK.kasparovKK.classOf φ) =
      ExtGroup.comap (φ : A →⋆ₙₐ[ℂ] B) :=
  (ExtGroup.kasparovCuntzData J).toExtKKAction_classOf hA hB φ

end GroupApproximation.Full.TWWSchafhauser
