import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVar
import GroupApproximation.Meta.AxiomGuard

/-!
# Substitutions on `R[s_σ]` for the cube reduction of the nil part of `K₂`

Lane `bh-met-34`.  Three substitution endomorphisms of `MvPolynomial σ R`, fixing `R`:

* `cubeKill R i`: `s_i ↦ 0`, `s_l ↦ s_l` for `l ≠ i`.
* `cubeUnit R i`: `s_i ↦ 1`, `s_l ↦ s_l` for `l ≠ i`.
* `cubeScale R i`: `s_i ↦ s_i`, `s_l ↦ s_l s_i` for `l ≠ i`.

Each ring-hom identity used by the cube step (module `ElemFPK2OneVarNilCube`) is proved by
`MvPolynomial.ringHom_ext`: it is enough to check on the constants and on each variable.

* `cubeKill_idem`: `π_i ∘ π_i = π_i`.
* `cubeKill_comp_comm`: `π_i ∘ π_j = π_j ∘ π_i`.
* `constantCoeff_comp_cubeKill`: `cc ∘ π_i = cc`.
* `cubeKill_comp_cubeScale`: `π_i ∘ θ_i = C ∘ cc`.
* `cubeUnit_comp_cubeScale_comp_cubeKill`: `ε_i ∘ θ_i ∘ π_i = π_i`.
* `cubeKill_comp_cubeScale_of_ne`: `π_i ∘ θ_j = θ_j ∘ π_i` for `i ≠ j`.
* `constantCoeff_comp_cubeScale`: `cc ∘ θ_i = cc`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section CubeMaps

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

variable (R) in
/-- The substitution `s_i ↦ 0`. -/
noncomputable def cubeKill (i : σ) : MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun l ↦ if l = i then 0 else MvPolynomial.X l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill

variable (R) in
/-- The substitution `s_i ↦ 1`. -/
noncomputable def cubeUnit (i : σ) : MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun l ↦ if l = i then 1 else MvPolynomial.X l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeUnit

variable (R) in
/-- The substitution `s_l ↦ s_l s_i` for `l ≠ i`, fixing `s_i`. -/
noncomputable def cubeScale (i : σ) : MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun l ↦
    if l = i then MvPolynomial.X l else MvPolynomial.X l * MvPolynomial.X i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeScale

theorem cubeKill_C (i : σ) (r : R) : cubeKill R i (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill_C

theorem cubeUnit_C (i : σ) (r : R) : cubeUnit R i (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeUnit_C

theorem cubeScale_C (i : σ) (r : R) : cubeScale R i (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeScale_C

theorem cubeKill_X_of_eq {i l : σ} (h : l = i) : cubeKill R i (MvPolynomial.X l) = 0 := by
  subst h
  exact (MvPolynomial.eval₂Hom_X' _ _ l).trans (if_pos rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill_X_of_eq

theorem cubeKill_X_of_ne {i l : σ} (h : l ≠ i) :
    cubeKill R i (MvPolynomial.X l) = MvPolynomial.X l :=
  (MvPolynomial.eval₂Hom_X' _ _ l).trans (if_neg h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill_X_of_ne

theorem cubeUnit_X_of_eq {i l : σ} (h : l = i) : cubeUnit R i (MvPolynomial.X l) = 1 := by
  subst h
  exact (MvPolynomial.eval₂Hom_X' _ _ l).trans (if_pos rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeUnit_X_of_eq

theorem cubeUnit_X_of_ne {i l : σ} (h : l ≠ i) :
    cubeUnit R i (MvPolynomial.X l) = MvPolynomial.X l :=
  (MvPolynomial.eval₂Hom_X' _ _ l).trans (if_neg h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeUnit_X_of_ne

theorem cubeScale_X_of_eq {i l : σ} (h : l = i) :
    cubeScale R i (MvPolynomial.X l) = MvPolynomial.X l :=
  (MvPolynomial.eval₂Hom_X' _ _ l).trans (if_pos h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeScale_X_of_eq

theorem cubeScale_X_of_ne {i l : σ} (h : l ≠ i) :
    cubeScale R i (MvPolynomial.X l) = MvPolynomial.X l * MvPolynomial.X i :=
  (MvPolynomial.eval₂Hom_X' _ _ l).trans (if_neg h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeScale_X_of_ne

/-- `π_i ∘ π_i = π_i`. -/
theorem cubeKill_idem (i : σ) : (cubeKill R i).comp (cubeKill R i) = cubeKill R i :=
  MvPolynomial.ringHom_ext (fun r ↦ by simp only [RingHom.comp_apply, cubeKill_C]) fun l ↦ by
    by_cases h : l = i
    · simp only [RingHom.comp_apply, cubeKill_X_of_eq h, map_zero]
    · simp only [RingHom.comp_apply, cubeKill_X_of_ne h]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill_idem

/-- `π_i ∘ π_j = π_j ∘ π_i`. -/
theorem cubeKill_comp_comm (i j : σ) :
    (cubeKill R i).comp (cubeKill R j) = (cubeKill R j).comp (cubeKill R i) :=
  MvPolynomial.ringHom_ext (fun r ↦ by simp only [RingHom.comp_apply, cubeKill_C]) fun l ↦ by
    by_cases hi : l = i
    · by_cases hj : l = j
      · simp only [RingHom.comp_apply, cubeKill_X_of_eq hi, cubeKill_X_of_eq hj, map_zero]
      · simp only [RingHom.comp_apply, cubeKill_X_of_eq hi, cubeKill_X_of_ne hj, map_zero]
    · by_cases hj : l = j
      · simp only [RingHom.comp_apply, cubeKill_X_of_ne hi, cubeKill_X_of_eq hj, map_zero]
      · simp only [RingHom.comp_apply, cubeKill_X_of_ne hi, cubeKill_X_of_ne hj]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill_comp_comm

/-- `cc ∘ π_i = cc`. -/
theorem constantCoeff_comp_cubeKill (i : σ) :
    MvPolynomial.constantCoeff.comp (cubeKill R i) = MvPolynomial.constantCoeff :=
  MvPolynomial.ringHom_ext (fun r ↦ by simp only [RingHom.comp_apply, cubeKill_C]) fun l ↦ by
    by_cases h : l = i
    · simp only [RingHom.comp_apply, cubeKill_X_of_eq h, map_zero, MvPolynomial.constantCoeff_X]
    · simp only [RingHom.comp_apply, cubeKill_X_of_ne h]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.constantCoeff_comp_cubeKill

/-- `π_i ∘ θ_i = C ∘ cc`. -/
theorem cubeKill_comp_cubeScale (i : σ) :
    (cubeKill R i).comp (cubeScale R i) = MvPolynomial.C.comp MvPolynomial.constantCoeff :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by
      simp only [RingHom.comp_apply, cubeScale_C, cubeKill_C, MvPolynomial.constantCoeff_C])
    fun l ↦ by
      by_cases h : l = i
      · simp only [RingHom.comp_apply, cubeScale_X_of_eq h, cubeKill_X_of_eq h,
          MvPolynomial.constantCoeff_X, map_zero]
      · simp only [RingHom.comp_apply, cubeScale_X_of_ne h, map_mul, cubeKill_X_of_ne h,
          cubeKill_X_of_eq (rfl : i = i), mul_zero, MvPolynomial.constantCoeff_X, map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill_comp_cubeScale

/-- `ε_i ∘ θ_i ∘ π_i = π_i`. -/
theorem cubeUnit_comp_cubeScale_comp_cubeKill (i : σ) :
    ((cubeUnit R i).comp (cubeScale R i)).comp (cubeKill R i) = cubeKill R i :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by simp only [RingHom.comp_apply, cubeKill_C, cubeScale_C, cubeUnit_C])
    fun l ↦ by
      by_cases h : l = i
      · simp only [RingHom.comp_apply, cubeKill_X_of_eq h, map_zero]
      · simp only [RingHom.comp_apply, cubeKill_X_of_ne h, cubeScale_X_of_ne h, map_mul,
          cubeUnit_X_of_ne h, cubeUnit_X_of_eq (rfl : i = i), mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeUnit_comp_cubeScale_comp_cubeKill

/-- `π_i ∘ θ_j = θ_j ∘ π_i` for `i ≠ j`. -/
theorem cubeKill_comp_cubeScale_of_ne {i j : σ} (h : i ≠ j) :
    (cubeKill R i).comp (cubeScale R j) = (cubeScale R j).comp (cubeKill R i) :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by simp only [RingHom.comp_apply, cubeKill_C, cubeScale_C]) fun l ↦ by
    by_cases hj : l = j
    · have hi : l ≠ i := fun hl ↦ h (hl.symm.trans hj)
      simp only [RingHom.comp_apply, cubeScale_X_of_eq hj, cubeKill_X_of_ne hi]
    · by_cases hi : l = i
      · simp only [RingHom.comp_apply, cubeScale_X_of_ne hj, map_mul, cubeKill_X_of_eq hi,
          cubeKill_X_of_ne (Ne.symm h), zero_mul, map_zero]
      · simp only [RingHom.comp_apply, cubeScale_X_of_ne hj, map_mul, cubeKill_X_of_ne hi,
          cubeKill_X_of_ne (Ne.symm h)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill_comp_cubeScale_of_ne

/-- `cc ∘ θ_i = cc`. -/
theorem constantCoeff_comp_cubeScale (i : σ) :
    MvPolynomial.constantCoeff.comp (cubeScale R i) = MvPolynomial.constantCoeff :=
  MvPolynomial.ringHom_ext (fun r ↦ by simp only [RingHom.comp_apply, cubeScale_C]) fun l ↦ by
    by_cases h : l = i
    · simp only [RingHom.comp_apply, cubeScale_X_of_eq h]
    · simp only [RingHom.comp_apply, cubeScale_X_of_ne h, map_mul,
        MvPolynomial.constantCoeff_X, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.constantCoeff_comp_cubeScale

end CubeMaps

end GroupApproximation.BooneHigman.Metabelian.ElemFP
