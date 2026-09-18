import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilLocal
import GroupApproximation.Meta.AxiomGuard

/-!
# The cone substitution `R[s_0] → R[s_0, s_1]`, `s_0 ↦ s_0 s_1`

Lane `bh-met-61`, helper module.  For a commutative ring `R` write `j = cubeCone R`, the substitution
`s_0 ↦ s_0 s_1` from `R[s_0]` to `R[s_0, s_1]`, and `r = cubeConeRetract R`, the substitution
`s_0 ↦ s_0`, `s_1 ↦ 1` back.

* `cubeConeRetract_comp_cubeCone`: `r ∘ j = id`, checked on constants and on `s_0`.
* `cubeKill_comp_cubeCone`: `π_i ∘ j = j ∘ π_0` for `i = 0, 1`, because `π_i (s_0 s_1) = 0`.
* `K2Map_cubeKill_K2Map_cubeCone`: so if `u ∈ K₂(N, R[s_0])` is killed by `s_0 ↦ 0`, then `j u` is
  killed by both `s_0 ↦ 0` and `s_1 ↦ 0`.
* `diesAfterPadding_of_diesAfterPadding_castLEEmb`: if the padding of `u` to rank `N' ≥ N` dies
  after padding, so does `u` (two paddings are one padding).

These hold for arbitrary rings, with no hypothesis.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section Cone

variable {R : Type*} [CommRing R]

variable (R) in
/-- The cone substitution `s_0 ↦ s_0 s_1`, from `R[s_0]` to `R[s_0, s_1]`. -/
noncomputable def cubeCone : MvPolynomial (Fin (0 + 1)) R →+* MvPolynomial (Fin (1 + 1)) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun _ ↦ MvPolynomial.X 0 * MvPolynomial.X 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeCone

variable (R) in
/-- The retraction `s_0 ↦ s_0`, `s_1 ↦ 1`, from `R[s_0, s_1]` to `R[s_0]`. -/
noncomputable def cubeConeRetract : MvPolynomial (Fin (1 + 1)) R →+* MvPolynomial (Fin (0 + 1)) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun l ↦ if l = 0 then MvPolynomial.X 0 else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeConeRetract

theorem cubeCone_C (r : R) : cubeCone R (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeCone_C

theorem cubeCone_X (l : Fin (0 + 1)) :
    cubeCone R (MvPolynomial.X l) = MvPolynomial.X 0 * MvPolynomial.X 1 :=
  MvPolynomial.eval₂Hom_X' _ _ l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeCone_X

theorem cubeConeRetract_C (r : R) : cubeConeRetract R (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeConeRetract_C

theorem cubeConeRetract_X (l : Fin (1 + 1)) :
    cubeConeRetract R (MvPolynomial.X l) = if l = 0 then MvPolynomial.X 0 else 1 :=
  MvPolynomial.eval₂Hom_X' _ _ l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeConeRetract_X

variable (R) in
/-- `r ∘ j = id`. -/
theorem cubeConeRetract_comp_cubeCone :
    (cubeConeRetract R).comp (cubeCone R) = RingHom.id (MvPolynomial (Fin (0 + 1)) R) :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by simp only [RingHom.comp_apply, cubeCone_C, cubeConeRetract_C, RingHom.id_apply])
    fun l ↦ by
      have hl : l = 0 := Fin.fin_one_eq_zero l
      subst hl
      rw [RingHom.comp_apply, cubeCone_X, map_mul, cubeConeRetract_X, cubeConeRetract_X,
        if_pos (rfl : (0 : Fin (1 + 1)) = 0), if_neg (show ¬((1 : Fin (1 + 1)) = 0) by decide),
        mul_one, RingHom.id_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeConeRetract_comp_cubeCone

/-- `π_i (s_0 s_1) = 0` for `i = 0, 1`. -/
theorem cubeKill_X_zero_mul_X_one (i : Fin (1 + 1)) :
    cubeKill R i (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin (1 + 1)) R) = 0 := by
  have hi : i = 0 ∨ i = 1 := by
    match i with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr rfl
    | ⟨n + 2, hn⟩ => exact absurd hn (by omega)
  rw [map_mul]
  rcases hi with rfl | rfl
  · rw [cubeKill_X_of_eq (R := R) (rfl : (0 : Fin (1 + 1)) = 0), zero_mul]
  · rw [cubeKill_X_of_eq (R := R) (rfl : (1 : Fin (1 + 1)) = 1), mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill_X_zero_mul_X_one

/-- `π_i ∘ j = j ∘ π_0` for `i = 0, 1`. -/
theorem cubeKill_comp_cubeCone (i : Fin (1 + 1)) :
    (cubeKill R i).comp (cubeCone R) = (cubeCone R).comp (cubeKill R (0 : Fin (0 + 1))) :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by simp only [RingHom.comp_apply, cubeCone_C, cubeKill_C])
    fun l ↦ by
      have hl : l = 0 := Fin.fin_one_eq_zero l
      subst hl
      rw [RingHom.comp_apply, RingHom.comp_apply, cubeCone_X, cubeKill_X_zero_mul_X_one,
        cubeKill_X_of_eq (R := R) (rfl : (0 : Fin (0 + 1)) = 0), map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cubeKill_comp_cubeCone

/-- If `u` is killed by `s_0 ↦ 0`, then `j u` is killed by `s_0 ↦ 0` and by `s_1 ↦ 0`. -/
theorem K2Map_cubeKill_K2Map_cubeCone {N : ℕ} {u : K2n N (MvPolynomial (Fin (0 + 1)) R)}
    (hu : K2Map (cubeKill R (0 : Fin (0 + 1))) u = 1) (i : Fin (1 + 1)) :
    K2Map (cubeKill R i) (K2Map (cubeCone R) u) = 1 := by
  rw [K2Map_K2Map, cubeKill_comp_cubeCone, ← K2Map_K2Map, hu, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Map_cubeKill_K2Map_cubeCone

end Cone

/-- If the padding of `u` to rank `N' ≥ N` dies after padding, then `u` dies after padding. -/
theorem diesAfterPadding_of_diesAfterPadding_castLEEmb {R : Type*} [Ring R] {N N' : ℕ}
    (h : N ≤ N') {u : K2n N R}
    (hu : K2DiesAfterPadding (K2IndexMap (R := R) (Fin.castLEEmb h) u)) :
    K2DiesAfterPadding u := by
  obtain ⟨M, hNM, hM⟩ := hu
  exact ⟨M, h.trans hNM, (K2IndexMap_castLEEmb_castLEEmb h hNM u).symm.trans hM⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_of_diesAfterPadding_castLEEmb

end GroupApproximation.BooneHigman.Metabelian.ElemFP
