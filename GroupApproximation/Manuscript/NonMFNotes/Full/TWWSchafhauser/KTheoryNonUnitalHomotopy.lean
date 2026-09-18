import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnital
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.NonUnitalHomotopy

/-!
# Homotopy invariance of `K₁` for non-unital C⋆-algebras

Lane `TWWSch3d3a`, work order `WO-TWWSchafhauser-3d3-1`, for
`thm:fixed-radical-membership` (`non_mf_group_notes.tex`, l.1376--1378). The source is
M. Rørdam, F. Larsen, N. Laustsen, *An introduction to K-theory for C⋆-algebras*, Proposition 8.1.4
(homotopy invariance of `K₁`) and §2.1.

Two non-unital ⋆-homomorphisms `φ ψ : J → J'` that are homotopic (`TWWKK.NHomotopic`, a pointwise
continuous path) induce the same map `KOneN J → KOneN J'`. For a unitary `v` over `J⁺`, the unitaries
`w t = (p t)⁺(v)` form a continuous path. So `(w 0)⁻¹ * w 1` lies in the identity component, and
`[w 0] = [w 1]` in `U_n(J'⁺)/U_n(J'⁺)₀`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

/- The matrix topology over `J⁺` uses the spectral order on the unitization. -/
attribute [local instance] unitizationOrder unitizationStarOrderedRing

/-- A continuous path `w : ℝ → G` in a topological group joins `1` to `(w 0)⁻¹ * w 1`. -/
theorem joined_inv_mul_of_continuous {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    {w : ℝ → G} (hw : Continuous w) : Joined (1 : G) ((w 0)⁻¹ * w 1) :=
  ⟨{ toFun := fun s => (w 0)⁻¹ * w (s : ℝ)
     continuous_toFun := continuous_const.mul (hw.comp continuous_subtype_val)
     source' := inv_mul_cancel (w 0)
     target' := rfl }⟩

section Path

variable {J J' : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra J']

/-- The unitizations along a pointwise continuous path of ⋆-homomorphisms are pointwise
continuous. -/
theorem continuous_starMap_apply {p : ℝ → (J →⋆ₙₐ[ℂ] J')}
    (hp : ∀ a : J, Continuous fun t : ℝ => p t a) (y : Unitization ℂ J) :
    Continuous fun t : ℝ => Unitization.starMap (p t) y := by
  show Continuous fun t : ℝ =>
    algebraMap ℂ (Unitization ℂ J') y.fst + ((p t y.snd : J') : Unitization ℂ J')
  exact continuous_const.add (Unitization.continuous_inr.comp (hp y.snd))

/-- Entrywise application of a pointwise continuous path of ⋆-homomorphisms to a unitary matrix
gives a continuous path of unitaries. -/
theorem continuous_matMapUnitary_starMap {p : ℝ → (J →⋆ₙₐ[ℂ] J')}
    (hp : ∀ a : J, Continuous fun t : ℝ => p t a) (n : ℕ)
    (v : unitary (CStarMat n (Unitization ℂ J))) :
    Continuous fun t : ℝ => matMapUnitary (Unitization.starMap (p t)) n v := by
  refine continuous_induced_rng.mpr (continuous_matrix fun i j => ?_)
  exact (continuous_starMap_apply hp ((v : CStarMat n (Unitization ℂ J)) i j)).congr fun _ => rfl

end Path

section KOne

variable {J J' : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra J']

/-- **Homotopy invariance of `K₁`** (RLL Proposition 8.1.4). Homotopic non-unital
⋆-homomorphisms induce the same map on `K₁`. -/
theorem KOneN.map_eq_of_nhomotopic {φ ψ : J →⋆ₙₐ[ℂ] J'} (h : TWWKK.NHomotopic φ ψ) :
    KOneN.map φ = KOneN.map ψ := by
  obtain ⟨p, hp, rfl, rfl⟩ := h
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨n, v, rfl⟩ := KOneN.exists_mk x
  have hj := joined_inv_mul_of_continuous (continuous_matMapUnitary_starMap hp n v)
  have key : (QuotientGroup.mk (matMapUnitary (Unitization.starMap (p 0)) n v) :
      KOneLevel (Unitization ℂ J') n) =
      QuotientGroup.mk (matMapUnitary (Unitization.starMap (p 1)) n v) :=
    QuotientGroup.eq.mpr (mem_unitaryComponentOne_iff.mpr hj)
  show KOneN.ofMul (kOneIota (Unitization ℂ J') n
      (QuotientGroup.mk (matMapUnitary (Unitization.starMap (p 0)) n v))) =
    KOneN.ofMul (kOneIota (Unitization ℂ J') n
      (QuotientGroup.mk (matMapUnitary (Unitization.starMap (p 1)) n v)))
  rw [key]

end KOne

end

end TWWSchafhauser
end Full
end GroupApproximation
