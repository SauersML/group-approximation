import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilFieldCone
import GroupApproximation.Meta.AxiomGuard

/-!
# The cone substitution in any number of variables: the cube gap descends from `k + 1` to `k`

Lane `bh-met-78`, helper module.  Lane `bh-met-61c` (module `ElemFPK2CubeNilFieldCone`) used the
cone `s_0 ↦ s_0 s_1` from `R[s_0]` to `R[s_0, s_1]` to derive the field case from the case of one
base variable.  Here the same device is set up for any number of variables.  For a commutative
ring `R` and `k : ℕ` let

* `j = cubeNilPosLocalCone R k : R[s_0..s_k] → R[s_0..s_{k+1}]`, `s_0 ↦ s_0 s_{k+1}` and
  `s_l ↦ s_l` for `1 ≤ l ≤ k`;
* `r = cubeNilPosLocalRetract R k : R[s_0..s_{k+1}] → R[s_0..s_k]`, `s_{k+1} ↦ 1` and
  `s_l ↦ s_l` for `l ≤ k`.

Results (no hypothesis on `R`):

* `cubeNilPosLocalRetract_comp_cone`: `r ∘ j = id`, checked on the constants and variables.
* `cubeNilPosLocal_cubeKill_castSucc_comp_cone`: `π_i ∘ j = j ∘ π_i` for `i ≤ k`, and
  `cubeNilPosLocal_cubeKill_last_comp_cone`: `π_{k+1} ∘ j = j ∘ π_0`, because
  `π_{k+1}(s_0 s_{k+1}) = 0 = j(π_0 s_0)`.
* `cubeNilPosLocal_cubeKill_cone`: so if `u ∈ K₂(N, R[s_0..s_k])` is killed by every `π_i`, then
  `j u ∈ K₂(N, R[s_0..s_{k+1}])` is killed by every `π_i`.
* `cubeNilPosLocal_dies_of_cone`: if `j u` dies after padding, so does `u = r (j u)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section Cone

variable {R : Type*} [CommRing R]

variable (R) in
/-- The cone substitution `s_0 ↦ s_0 s_{k+1}`, `s_l ↦ s_l` (`1 ≤ l ≤ k`), from `R[s_0..s_k]` to
`R[s_0..s_{k+1}]`. -/
noncomputable def cubeNilPosLocalCone (k : ℕ) :
    MvPolynomial (Fin (k + 1)) R →+* MvPolynomial (Fin (k + 1 + 1)) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun l ↦
    if l = 0 then MvPolynomial.X (Fin.castSucc 0) * MvPolynomial.X (Fin.last (k + 1))
    else MvPolynomial.X (Fin.castSucc l)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalCone

variable (R) in
/-- The retraction `s_{k+1} ↦ 1`, `s_l ↦ s_l` (`l ≤ k`), from `R[s_0..s_{k+1}]` to
`R[s_0..s_k]`. -/
noncomputable def cubeNilPosLocalRetract (k : ℕ) :
    MvPolynomial (Fin (k + 1 + 1)) R →+* MvPolynomial (Fin (k + 1)) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun l ↦
    Fin.lastCases (motive := fun _ ↦ MvPolynomial (Fin (k + 1)) R) 1
      (fun i ↦ MvPolynomial.X i) l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalRetract

theorem cubeNilPosLocalCone_C (k : ℕ) (r : R) :
    cubeNilPosLocalCone R k (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalCone_C

theorem cubeNilPosLocalCone_X (k : ℕ) (l : Fin (k + 1)) :
    cubeNilPosLocalCone R k (MvPolynomial.X l) =
      if l = 0 then MvPolynomial.X (Fin.castSucc 0) * MvPolynomial.X (Fin.last (k + 1))
      else MvPolynomial.X (Fin.castSucc l) :=
  MvPolynomial.eval₂Hom_X' _ _ l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalCone_X

theorem cubeNilPosLocalCone_X_zero (k : ℕ) :
    cubeNilPosLocalCone R k (MvPolynomial.X 0) =
      MvPolynomial.X (Fin.castSucc 0) * MvPolynomial.X (Fin.last (k + 1)) := by
  rw [cubeNilPosLocalCone_X, if_pos rfl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalCone_X_zero

theorem cubeNilPosLocalCone_X_of_ne {k : ℕ} {l : Fin (k + 1)} (hl : l ≠ 0) :
    cubeNilPosLocalCone R k (MvPolynomial.X l) = MvPolynomial.X (Fin.castSucc l) := by
  rw [cubeNilPosLocalCone_X, if_neg hl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalCone_X_of_ne

theorem cubeNilPosLocalRetract_C (k : ℕ) (r : R) :
    cubeNilPosLocalRetract R k (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalRetract_C

theorem cubeNilPosLocalRetract_X (k : ℕ) (l : Fin (k + 1 + 1)) :
    cubeNilPosLocalRetract R k (MvPolynomial.X l) =
      Fin.lastCases (motive := fun _ ↦ MvPolynomial (Fin (k + 1)) R) 1
        (fun i ↦ MvPolynomial.X i) l :=
  MvPolynomial.eval₂Hom_X' _ _ l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalRetract_X

theorem cubeNilPosLocalRetract_X_last (k : ℕ) :
    cubeNilPosLocalRetract R k (MvPolynomial.X (Fin.last (k + 1))) = 1 := by
  rw [cubeNilPosLocalRetract_X, Fin.lastCases_last]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalRetract_X_last

theorem cubeNilPosLocalRetract_X_castSucc (k : ℕ) (i : Fin (k + 1)) :
    cubeNilPosLocalRetract R k (MvPolynomial.X (Fin.castSucc i)) = MvPolynomial.X i := by
  rw [cubeNilPosLocalRetract_X, Fin.lastCases_castSucc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalRetract_X_castSucc

variable (R) in
/-- `r ∘ j = id`. -/
theorem cubeNilPosLocalRetract_comp_cone (k : ℕ) :
    (cubeNilPosLocalRetract R k).comp (cubeNilPosLocalCone R k) =
      RingHom.id (MvPolynomial (Fin (k + 1)) R) :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by
      simp only [RingHom.comp_apply, cubeNilPosLocalCone_C, cubeNilPosLocalRetract_C,
        RingHom.id_apply])
    fun l ↦ by
      rw [RingHom.comp_apply, RingHom.id_apply]
      by_cases hl : l = 0
      · subst hl
        rw [cubeNilPosLocalCone_X_zero, map_mul, cubeNilPosLocalRetract_X_castSucc,
          cubeNilPosLocalRetract_X_last, mul_one]
      · rw [cubeNilPosLocalCone_X_of_ne hl, cubeNilPosLocalRetract_X_castSucc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeNilPosLocalRetract_comp_cone

end Cone

end GroupApproximation.BooneHigman.Metabelian.ElemFP
