import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilFieldPos
import GroupApproximation.Meta.AxiomGuard

/-!
# The general cone substitution `R[s_0..s_n] → R[s_0..s_{n+1}]`, `s_0 ↦ s_0 s_{n+1}`

Lane `bh-met-81`, helper module (ring-generic, no hypothesis).  Module
`ElemFPK2CubeNilFieldCone` has the cone `s_0 ↦ s_0 s_1` for one variable only.  Here, for any
commutative ring `R` and any `n`, write `j = czCubeResFieldCone R n`:
`s_0 ↦ s_0 s_{n+1}` and `s_i ↦ s_i` for `1 ≤ i ≤ n`, and `r = czCubeResFieldConeRetract R n`:
`s_l ↦ s_l` for `l ≤ n` and `s_{n+1} ↦ 1`.

* `czCubeResField_retract_comp_cone`: `r ∘ j = id`.
* `czCubeResField_cubeKill_castSucc_comp_cone`: `π_i ∘ j = j ∘ π_i` for `i ≤ n`.
* `czCubeResField_cubeKill_last_comp_cone`: `π_{n+1} ∘ j = j ∘ π_0`, since `π_{n+1}(s_0 s_{n+1}) = 0`.
* `czCubeResField_K2Map_cubeKill_cone`: if `u ∈ K₂(N, R[s_0..s_n])` is killed by every `π_i`,
  then `j u` is killed by every `π_i`, `i ≤ n + 1`.
* `czCubeResField_dies_of_cone_step`: if every element of `K₂(N, R[s_0..s_{n+1}])` killed by every
  `π_i` dies after padding, so does every such element of `K₂(N, R[s_0..s_n])` (apply `r`).
* `czCubeResField_dies_of_cone_iter`: iterating, the cube form with `n + r + 1` variables at a
  fixed rank `N` gives the cube form with `n + 1` variables at the same rank `N`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Cone

variable {R : Type*} [CommRing R]

variable (R) in
/-- The cone substitution `s_0 ↦ s_0 s_{n+1}`, `s_i ↦ s_i` (`1 ≤ i ≤ n`), from `R[s_0..s_n]` to
`R[s_0..s_{n+1}]`. -/
noncomputable def czCubeResFieldCone (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin (n + 1 + 1)) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i ↦
    if i = 0 then MvPolynomial.X (Fin.castSucc i) * MvPolynomial.X (Fin.last (n + 1))
    else MvPolynomial.X (Fin.castSucc i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone

variable (R) in
/-- The retraction `s_l ↦ s_l` (`l ≤ n`), `s_{n+1} ↦ 1`, from `R[s_0..s_{n+1}]` to
`R[s_0..s_n]`. -/
noncomputable def czCubeResFieldConeRetract (n : ℕ) :
    MvPolynomial (Fin (n + 1 + 1)) R →+* MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun l ↦
    if h : (l : ℕ) < n + 1 then MvPolynomial.X (⟨(l : ℕ), h⟩ : Fin (n + 1)) else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract

theorem czCubeResFieldCone_C {n : ℕ} (r : R) :
    czCubeResFieldCone R n (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone_C

theorem czCubeResFieldCone_X {n : ℕ} (i : Fin (n + 1)) :
    czCubeResFieldCone R n (MvPolynomial.X i) =
      if i = 0 then MvPolynomial.X (Fin.castSucc i) * MvPolynomial.X (Fin.last (n + 1))
      else MvPolynomial.X (Fin.castSucc i) :=
  MvPolynomial.eval₂Hom_X' _ _ i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone_X

theorem czCubeResFieldCone_X_zero {n : ℕ} :
    czCubeResFieldCone R n (MvPolynomial.X 0) =
      MvPolynomial.X (Fin.castSucc 0) * MvPolynomial.X (Fin.last (n + 1)) :=
  (czCubeResFieldCone_X (R := R) (0 : Fin (n + 1))).trans (if_pos rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone_X_zero

theorem czCubeResFieldCone_X_of_ne {n : ℕ} {i : Fin (n + 1)} (h : i ≠ 0) :
    czCubeResFieldCone R n (MvPolynomial.X i) = MvPolynomial.X (Fin.castSucc i) :=
  (czCubeResFieldCone_X (R := R) i).trans (if_neg h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone_X_of_ne

theorem czCubeResFieldConeRetract_C {n : ℕ} (r : R) :
    czCubeResFieldConeRetract R n (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract_C

theorem czCubeResFieldConeRetract_X {n : ℕ} (l : Fin (n + 1 + 1)) :
    czCubeResFieldConeRetract R n (MvPolynomial.X l) =
      if h : (l : ℕ) < n + 1 then MvPolynomial.X (⟨(l : ℕ), h⟩ : Fin (n + 1)) else 1 :=
  MvPolynomial.eval₂Hom_X' _ _ l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract_X

theorem czCubeResFieldConeRetract_X_castSucc {n : ℕ} (i : Fin (n + 1)) :
    czCubeResFieldConeRetract R n (MvPolynomial.X (Fin.castSucc i)) = MvPolynomial.X i := by
  rw [czCubeResFieldConeRetract_X]
  exact dif_pos (show ((Fin.castSucc i : Fin (n + 1 + 1)) : ℕ) < n + 1 from i.isLt)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract_X_castSucc

theorem czCubeResFieldConeRetract_X_last {n : ℕ} :
    czCubeResFieldConeRetract R n (MvPolynomial.X (Fin.last (n + 1))) = 1 := by
  rw [czCubeResFieldConeRetract_X]
  exact dif_neg (show ¬((Fin.last (n + 1) : Fin (n + 1 + 1)) : ℕ) < n + 1 from Nat.lt_irrefl _)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract_X_last

variable (R) in
/-- `r ∘ j = id`. -/
theorem czCubeResField_retract_comp_cone (n : ℕ) :
    (czCubeResFieldConeRetract R n).comp (czCubeResFieldCone R n) =
      RingHom.id (MvPolynomial (Fin (n + 1)) R) :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by
      simp only [RingHom.comp_apply, czCubeResFieldCone_C, czCubeResFieldConeRetract_C,
        RingHom.id_apply])
    fun l ↦ by
      rw [RingHom.comp_apply, RingHom.id_apply]
      by_cases hl0 : l = 0
      · subst hl0
        rw [czCubeResFieldCone_X_zero, map_mul, czCubeResFieldConeRetract_X_castSucc,
          czCubeResFieldConeRetract_X_last, mul_one]
      · rw [czCubeResFieldCone_X_of_ne hl0, czCubeResFieldConeRetract_X_castSucc]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResField_retract_comp_cone

/-- `π_i ∘ j = j ∘ π_i` for `i ≤ n`. -/
theorem czCubeResField_cubeKill_castSucc_comp_cone {n : ℕ} (i : Fin (n + 1)) :
    (cubeKill R (Fin.castSucc i)).comp (czCubeResFieldCone R n) =
      (czCubeResFieldCone R n).comp (cubeKill R i) :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by simp only [RingHom.comp_apply, czCubeResFieldCone_C, cubeKill_C])
    fun l ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply]
      by_cases hl0 : l = 0
      · subst hl0
        by_cases hi : (0 : Fin (n + 1)) = i
        · subst hi
          rw [czCubeResFieldCone_X_zero, map_mul, cubeKill_X_of_eq (R := R) rfl, zero_mul,
            cubeKill_X_of_eq (R := R) rfl, map_zero]
        · rw [czCubeResFieldCone_X_zero, map_mul,
            cubeKill_X_of_ne (R := R)
              (show Fin.castSucc (0 : Fin (n + 1)) ≠ Fin.castSucc i from
                fun h ↦ hi (Fin.castSucc_inj.mp h)),
            cubeKill_X_of_ne (R := R) (Fin.castSucc_ne_last i).symm,
            cubeKill_X_of_ne (R := R) hi, czCubeResFieldCone_X_zero]
      · rw [czCubeResFieldCone_X_of_ne hl0]
        by_cases hi : l = i
        · subst hi
          rw [cubeKill_X_of_eq (R := R) rfl, cubeKill_X_of_eq (R := R) rfl, map_zero]
        · rw [cubeKill_X_of_ne (R := R)
              (show Fin.castSucc l ≠ Fin.castSucc i from fun h ↦ hi (Fin.castSucc_inj.mp h)),
            cubeKill_X_of_ne (R := R) hi, czCubeResFieldCone_X_of_ne hl0]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResField_cubeKill_castSucc_comp_cone

/-- `π_{n+1} ∘ j = j ∘ π_0`, because `π_{n+1}(s_0 s_{n+1}) = 0`. -/
theorem czCubeResField_cubeKill_last_comp_cone {n : ℕ} :
    (cubeKill R (Fin.last (n + 1))).comp (czCubeResFieldCone R n) =
      (czCubeResFieldCone R n).comp (cubeKill R (0 : Fin (n + 1))) :=
  MvPolynomial.ringHom_ext
    (fun r ↦ by simp only [RingHom.comp_apply, czCubeResFieldCone_C, cubeKill_C])
    fun l ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply]
      by_cases hl0 : l = 0
      · subst hl0
        rw [czCubeResFieldCone_X_zero, map_mul, cubeKill_X_of_eq (R := R) rfl, mul_zero,
          cubeKill_X_of_eq (R := R) rfl, map_zero]
      · rw [czCubeResFieldCone_X_of_ne hl0, cubeKill_X_of_ne (R := R) (Fin.castSucc_ne_last l),
          cubeKill_X_of_ne (R := R) hl0, czCubeResFieldCone_X_of_ne hl0]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResField_cubeKill_last_comp_cone

/-- If `u` is killed by every `π_i`, `i ≤ n`, then `j u` is killed by every `π_i`, `i ≤ n + 1`. -/
theorem czCubeResField_K2Map_cubeKill_cone {n N : ℕ}
    {u : K2n N (MvPolynomial (Fin (n + 1)) R)}
    (hu : ∀ i : Fin (n + 1), K2Map (cubeKill R i) u = 1) (j : Fin (n + 1 + 1)) :
    K2Map (cubeKill R j) (K2Map (czCubeResFieldCone R n) u) = 1 := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [K2Map_K2Map, czCubeResField_cubeKill_castSucc_comp_cone, ← K2Map_K2Map, hu i, map_one]
  · rw [K2Map_K2Map, czCubeResField_cubeKill_last_comp_cone, ← K2Map_K2Map, hu 0, map_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResField_K2Map_cubeKill_cone

/-- **One cone step.**  If every element of `K₂(N, R[s_0..s_{n+1}])` killed by every `π_i` dies
after padding, then so does every element of `K₂(N, R[s_0..s_n])` killed by every `π_i`: its cone
image dies, and the retraction `r` with `r ∘ j = id` carries this back. -/
theorem czCubeResField_dies_of_cone_step {N : ℕ} (n : ℕ)
    (h : ∀ v : K2n N (MvPolynomial (Fin (n + 1 + 1)) R),
      (∀ j : Fin (n + 1 + 1), K2Map (cubeKill R j) v = 1) → K2DiesAfterPadding v)
    (u : K2n N (MvPolynomial (Fin (n + 1)) R))
    (hu : ∀ i : Fin (n + 1), K2Map (cubeKill R i) u = 1) : K2DiesAfterPadding u := by
  have hd := diesAfterPadding_K2Map (czCubeResFieldConeRetract R n)
    (h _ (czCubeResField_K2Map_cubeKill_cone hu))
  rwa [K2Map_K2Map_of_comp_eq_id _ _ (czCubeResField_retract_comp_cone R n)] at hd

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResField_dies_of_cone_step

/-- **Iterated cone.**  At a fixed rank `N`, the cube form with `n + r + 1` variables gives the
cube form with `n + 1` variables. -/
theorem czCubeResField_dies_of_cone_iter {N : ℕ} (n r : ℕ)
    (h : ∀ v : K2n N (MvPolynomial (Fin (n + r + 1)) R),
      (∀ j : Fin (n + r + 1), K2Map (cubeKill R j) v = 1) → K2DiesAfterPadding v) :
    ∀ u : K2n N (MvPolynomial (Fin (n + 1)) R),
      (∀ i : Fin (n + 1), K2Map (cubeKill R i) u = 1) → K2DiesAfterPadding u := by
  induction r with
  | zero => exact h
  | succ r ih => exact ih (czCubeResField_dies_of_cone_step (n + r) h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResField_dies_of_cone_iter

end Cone

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
