import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCorner
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCornerShift.CornerMap
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# The corner endomorphism is inner after one stabilization (sk-leavitt-36b, 1)

Let `R` be a ring with a Leavitt family `L`, and `σ_r = fiveStepCornerHom L r` the corner
endomorphism of `St_n(R)`: `x_{rj}(a) ↦ x_{rj}(s₀ a)`, `x_{ir}(a) ↦ x_{ir}(a t₀)`, and the other
generators are fixed.  Write `pad = stab n R : St_n(R) → St_{n+1}(R)` (along `Fin.castSucc`).

Main result (`fiveStepRankFourFix_conj_stab`), unconditional:

  `C · pad(w) · C⁻¹ = pad(σ_r w)` for every `w ∈ St_n(R)`,

where `C = cornerConj (castSucc r) (last n) s₀ t₀` is an explicit product of five root elements
in the `(castSucc r, last n)` plane.  So `σ_r` becomes inner after one stabilization.

## Route

* `σ_r` is the diagonal corner map `x_{ij}(a) ↦ x_{ij}(σ'ᵢ a τ'ⱼ)` of lane LVCornerShift, with
  `σ' = (s₀ at r, 1 elsewhere)` and `τ' = (t₀ at r, 1 elsewhere)`
  (`fiveStepRankFourFix_cornerMap_eq`).  It is checked on generators.
* The corner map with diagonals `1, 1` is the identity (`Full.LVCornerShift.cornerMap_eq_self`).
* Stabilized once, conjugation by `cornerConj` turns the corner map with diagonals `(σ, τ)` into
  the one with `(σ', τ')`, for `σ' r = s₀ σ r` and `τ' r = τ r t₀`
  (`Full.LVCornerShift.cornerConj_castSuccStab_cornerMap`).  It needs only `t₀ s₀ = 1`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ}

/-- The left diagonal of `σ_r`: `s₀` at the index `r` and `1` elsewhere. -/
def fiveStepRankFourFixLeft (r i : Fin n) : R :=
  if i = r then L.s0 else 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFixLeft

/-- The right diagonal of `σ_r`: `t₀` at the index `r` and `1` elsewhere. -/
def fiveStepRankFourFixRight (r i : Fin n) : R :=
  if i = r then L.t0 else 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFixRight

theorem fiveStepRankFourFixLeft_of_eq (r : Fin n) {i : Fin n} (hi : i = r) :
    fiveStepRankFourFixLeft L r i = L.s0 :=
  if_pos hi

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFixLeft_of_eq

theorem fiveStepRankFourFixLeft_of_ne (r : Fin n) {i : Fin n} (hi : ¬ i = r) :
    fiveStepRankFourFixLeft L r i = 1 :=
  if_neg hi

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFixLeft_of_ne

theorem fiveStepRankFourFixRight_of_eq (r : Fin n) {i : Fin n} (hi : i = r) :
    fiveStepRankFourFixRight L r i = L.t0 :=
  if_pos hi

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFixRight_of_eq

theorem fiveStepRankFourFixRight_of_ne (r : Fin n) {i : Fin n} (hi : ¬ i = r) :
    fiveStepRankFourFixRight L r i = 1 :=
  if_neg hi

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFixRight_of_ne

/-- The two diagonals are inverse on the left: `τ'ᵢ σ'ᵢ = 1`, from `t₀ s₀ = 1`. -/
theorem fiveStepRankFourFix_right_mul_left (r i : Fin n) :
    fiveStepRankFourFixRight L r i * fiveStepRankFourFixLeft L r i = 1 := by
  by_cases hi : i = r
  · rw [fiveStepRankFourFixRight_of_eq L r hi, fiveStepRankFourFixLeft_of_eq L r hi, L.t0_s0]
  · rw [fiveStepRankFourFixRight_of_ne L r hi, fiveStepRankFourFixLeft_of_ne L r hi, one_mul]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_right_mul_left

/-- **`σ_r` is a diagonal corner map**, with diagonals `(s₀ at r)` and `(t₀ at r)`. -/
theorem fiveStepRankFourFix_cornerMap_eq (r : Fin n) (w : SteinbergGroup (Fin n) R) :
    Full.LVCornerShift.cornerMap (fiveStepRankFourFixLeft L r) (fiveStepRankFourFixRight L r)
        (fiveStepRankFourFix_right_mul_left L r) w = fiveStepCornerHom L r w := by
  have hh : Full.LVCornerShift.cornerMap (fiveStepRankFourFixLeft L r)
      (fiveStepRankFourFixRight L r) (fiveStepRankFourFix_right_mul_left L r) =
      fiveStepCornerHom L r := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change Full.LVCornerShift.cornerMap (fiveStepRankFourFixLeft L r)
        (fiveStepRankFourFixRight L r) (fiveStepRankFourFix_right_mul_left L r) (x i j hij a) =
      fiveStepCornerHom L r (x i j hij a)
    rw [Full.LVCornerShift.cornerMap_x, fiveStepCornerHom_x]
    by_cases hi : i = r
    · have hj : ¬ j = r := fun h => hij (hi.trans h.symm)
      rw [fiveStepRankFourFixLeft_of_eq L r hi, fiveStepRankFourFixRight_of_ne L r hj, mul_one,
        fiveStepCornerCoeff_of_row L r a hi]
    · by_cases hj : j = r
      · rw [fiveStepRankFourFixLeft_of_ne L r hi, fiveStepRankFourFixRight_of_eq L r hj, one_mul,
          fiveStepCornerCoeff_of_col L r a hi hj]
      · rw [fiveStepRankFourFixLeft_of_ne L r hi, fiveStepRankFourFixRight_of_ne L r hj, one_mul,
          mul_one, fiveStepCornerCoeff_of_plain L r a hi hj]
  exact DFunLike.congr_fun hh w

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_cornerMap_eq

/-- **`σ_r` becomes inner after one stabilization.**  Conjugation by the corner element
`C = cornerConj (castSucc r) (last n) s₀ t₀` of `St_{n+1}(R)` restricts on `pad(St_n(R))` to
`pad ∘ σ_r`.  Unconditional: only `t₀ s₀ = 1` is used. -/
theorem fiveStepRankFourFix_conj_stab (r : Fin n) (w : SteinbergGroup (Fin n) R) :
    Full.LVCornerShift.cornerConj (Fin.castSucc_ne_last r) L.s0 L.t0 *
        BooneHigman.SteinbergBasic.stab n R w *
        (Full.LVCornerShift.cornerConj (Fin.castSucc_ne_last r) L.s0 L.t0)⁻¹ =
      BooneHigman.SteinbergBasic.stab n R (fiveStepCornerHom L r w) := by
  have step := Full.LVCornerShift.cornerConj_castSuccStab_cornerMap L.t0_s0 r
    (fun _ : Fin n => (1 : R)) (fun _ : Fin n => (1 : R)) (fiveStepRankFourFixLeft L r)
    (fiveStepRankFourFixRight L r) (fun _ => mul_one _) (fiveStepRankFourFix_right_mul_left L r)
    (show fiveStepRankFourFixLeft L r r = L.s0 * 1 by
      rw [fiveStepRankFourFixLeft_of_eq L r rfl, mul_one])
    (show fiveStepRankFourFixRight L r r = 1 * L.t0 by
      rw [fiveStepRankFourFixRight_of_eq L r rfl, one_mul])
    (fun j hj => fiveStepRankFourFixLeft_of_ne L r hj)
    (fun j hj => fiveStepRankFourFixRight_of_ne L r hj) w
  have e1 : Full.LVCornerShift.cornerMap (fun _ : Fin n => (1 : R)) (fun _ : Fin n => (1 : R))
      (fun _ => mul_one _) w = w :=
    Full.LVCornerShift.cornerMap_eq_self _ _ _ (fun _ => rfl) (fun _ => rfl) w
  rw [e1, fiveStepRankFourFix_cornerMap_eq L r w] at step
  exact step

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_conj_stab

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
