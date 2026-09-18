import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateTorsion
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDiagDilateSt
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Dilation and the Steinberg projection

Lane `bh-met-90h`, second helper module.

* `k2Dilate_mapMatrix_eq_one_of_stDies`: if `φ g` dies after padding, then the matrix of `g`
  goes to `1` under `φ`.  Padding of matrices is injective at `1`.
* `k2Dilate_mem_K2_of_mapMatrix`: if the matrix of `g` goes to `1` under `φ`, then
  `φ g ∈ K₂`.
* Ring-map identities for `μ_c = k2CubeDilate_scale A c`: `μ_c ∘ μ_d = μ_{d c}`,
  `ev₀ ∘ μ_c = ev₀`, and `φ ∘ μ_c = μ_{φ c} ∘ φ` coefficientwise.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section DilateProj

variable {I R T : Type*} [Fintype I] [DecidableEq I] [Ring R] [Ring T]

/-- The matrix of `φ g` is `φ` applied to the matrix of `g`. -/
theorem k2Dilate_coe_projection_ringMap (φ : R →+* T) (g : SteinbergGroup I R) :
    ((SteinbergGroup.projection (SteinbergGroup.ringMap φ g) : (Matrix I I T)ˣ) : Matrix I I T) =
      φ.mapMatrix ((SteinbergGroup.projection g : (Matrix I I R)ˣ) : Matrix I I R) := by
  have h := congrArg (fun x : elementaryGroup I T ↦ ((x : (Matrix I I T)ˣ) : Matrix I I T))
    (projection_ringMap φ g)
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_coe_projection_ringMap

/-- If the matrix of `g` goes to `1` under `φ`, then `φ g ∈ K₂`. -/
theorem k2Dilate_mem_K2_of_mapMatrix (φ : R →+* T) (g : SteinbergGroup I R)
    (h : φ.mapMatrix ((SteinbergGroup.projection g : (Matrix I I R)ˣ) : Matrix I I R) = 1) :
    SteinbergGroup.ringMap φ g ∈ K2 I T := by
  rw [mem_K2_iff]
  apply Subtype.ext
  apply Units.ext
  exact (k2Dilate_coe_projection_ringMap φ g).trans h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_mem_K2_of_mapMatrix

end DilateProj

section DilatePadProj

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Ring R]

/-- The matrix of a padded elementary matrix is the padded matrix. -/
theorem k2Dilate_coe_elementaryPad (e : ι ↪ κ) (x : elementaryGroup ι R) :
    ((ElementaryPadding.elementaryPad e x : (Matrix κ κ R)ˣ) : Matrix κ κ R) =
      ElementaryPadding.padHom e ((x : (Matrix ι ι R)ˣ) : Matrix ι ι R) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_coe_elementaryPad

end DilatePadProj

section DilateStDies

variable {R T : Type*} [Ring R] [Ring T] {N : ℕ}

/-- If `φ g` dies after padding, then the matrix of `g` goes to `1` under `φ`. -/
theorem k2Dilate_mapMatrix_eq_one_of_stDies (φ : R →+* T) (g : SteinbergGroup (Fin N) R)
    (h : cubeDiagDilate_StDies (SteinbergGroup.ringMap φ g)) :
    φ.mapMatrix
      ((SteinbergGroup.projection g : (Matrix (Fin N) (Fin N) R)ˣ) : Matrix (Fin N) (Fin N) R) =
        1 := by
  obtain ⟨M, hNM, hM⟩ := h
  have h1 : SteinbergGroup.projection (SteinbergGroup.indexMap (R := T) (Fin.castLEEmb hNM)
      (SteinbergGroup.ringMap φ g)) = 1 := by
    rw [hM, map_one]
  rw [projection_indexMap] at h1
  have h2 := congrArg
    (fun x : elementaryGroup (Fin M) T ↦ ((x : (Matrix (Fin M) (Fin M) T)ˣ) :
      Matrix (Fin M) (Fin M) T)) h1
  apply k2Dilate_eq_one_of_padHom (Fin.castLEEmb hNM)
  rw [← k2Dilate_coe_projection_ringMap φ g, ← k2Dilate_coe_elementaryPad]
  exact h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_mapMatrix_eq_one_of_stDies

end DilateStDies

section DilateScale

variable {A : Type*} [CommRing A]

/-- `μ_c ∘ μ_d = μ_{d c}`. -/
theorem k2Dilate_scale_comp (c d : A) :
    (k2CubeDilate_scale A c).comp (k2CubeDilate_scale A d) = k2CubeDilate_scale A (d * c) :=
  Polynomial.ringHom_ext
    (fun a ↦ by
      rw [RingHom.comp_apply, k2CubeDilate_scale_C d a, k2CubeDilate_scale_C c a,
        k2CubeDilate_scale_C (d * c) a])
    (by
      rw [RingHom.comp_apply, k2CubeDilate_scale_X d, map_mul, k2CubeDilate_scale_C c d,
        k2CubeDilate_scale_X c, k2CubeDilate_scale_X (d * c), Polynomial.C_mul, mul_assoc])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_scale_comp

/-- `ev₀ ∘ μ_c = ev₀`. -/
theorem k2Dilate_evalZero_comp_scale (c : A) :
    (Polynomial.evalRingHom (0 : A)).comp (k2CubeDilate_scale A c) = Polynomial.evalRingHom 0 :=
  Polynomial.ringHom_ext
    (fun a ↦ by rw [RingHom.comp_apply, k2CubeDilate_scale_C])
    (by
      rw [RingHom.comp_apply, k2CubeDilate_scale_X, Polynomial.coe_evalRingHom,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_evalZero_comp_scale

/-- A coefficient map commutes with dilation: `φ ∘ μ_c = μ_{φ c} ∘ φ`. -/
theorem k2Dilate_map_comp_scale {T : Type*} [CommRing T] (φ : A →+* T) (c : A) :
    (Polynomial.mapRingHom φ).comp (k2CubeDilate_scale A c) =
      (k2CubeDilate_scale T (φ c)).comp (Polynomial.mapRingHom φ) :=
  Polynomial.ringHom_ext
    (fun a ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, k2CubeDilate_scale_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, k2CubeDilate_scale_C])
    (by
      rw [RingHom.comp_apply, RingHom.comp_apply, k2CubeDilate_scale_X,
        Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        k2CubeDilate_scale_X])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_map_comp_scale

end DilateScale

end GroupApproximation.BooneHigman.Metabelian.ElemFP
