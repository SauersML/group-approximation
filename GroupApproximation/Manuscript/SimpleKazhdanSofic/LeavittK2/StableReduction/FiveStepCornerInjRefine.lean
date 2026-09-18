import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCornerInjTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# Corner endomorphisms commute with the Leavitt refinement away from the split index
(sk-leavitt-34c)

Let `D_r = LeavittFP.refineHom L r : St_n(R) → St_{n+1}(R)` split the index `r` into
`castSucc r` and `last n`, and let `σ_j = fiveStepCornerHom L j`.  If `j ≠ r`, then

  `σ_{castSucc j} ∘ D_r = D_r ∘ σ_j`   (`fiveStepCornerInj_cornerHom_comp_refineHom`).

Proof on generators `xᵢⱼ(a)`, by cases:
* `i = r` (so `i ≠ j₀`): both sides are `x_{r j}(t₀ c) · x_{last, j}(t₁ c)`, with `c = a t₀` if
  `j = j₀` and `c = a` otherwise; this is associativity `(t₀ a) t₀ = t₀ (a t₀)`;
* `j = r`, `i ≠ r`: both sides are `x_{i r}(c s₀) · x_{i, last}(c s₁)`, with `c = s₀ a` if `i = j₀`;
* otherwise the root is untouched by `D_r` and the corner coefficient is `castSucc`-invariant.

No Leavitt relation is used: the refinement acts on the split index, `σ_j` on the index `j`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ}

/-- **Refinement and corner endomorphism commute** when the corner index `j₀` is not the split
index `r`: `σ_{castSucc j₀} ∘ D_r = D_r ∘ σ_{j₀}`. -/
theorem fiveStepCornerInj_cornerHom_comp_refineHom (r j₀ : Fin n) (hj : j₀ ≠ r) :
    (fiveStepCornerHom L (Fin.castSucc j₀)).comp (LeavittFP.refineHom L r) =
      (LeavittFP.refineHom L r).comp (fiveStepCornerHom L j₀) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change fiveStepCornerHom L (Fin.castSucc j₀) (LeavittFP.refineHom L r (x i j hij a)) =
    LeavittFP.refineHom L r (fiveStepCornerHom L j₀ (x i j hij a))
  rw [LeavittFP.refineHom_x, fiveStepCornerHom_x, LeavittFP.refineHom_x]
  have hl : ¬ Fin.last n = Fin.castSucc j₀ := (Fin.castSucc_ne_last j₀).symm
  by_cases hi : i = r
  · have hi0 : ¬ i = j₀ := fun h => hj (h.symm.trans hi)
    have hci : ¬ Fin.castSucc i = Fin.castSucc j₀ := fun h => hi0 (Fin.castSucc_injective n h)
    rw [LeavittFP.refineRoot_of_row L r hij a hi, LeavittFP.refineRoot_of_row L r hij _ hi,
      map_mul, fiveStepCornerHom_x, fiveStepCornerHom_x]
    by_cases hj0 : j = j₀
    · rw [fiveStepCornerCoeff_of_col L j₀ a hi0 hj0,
        fiveStepCornerCoeff_of_col L (Fin.castSucc j₀) (L.t0 * a) hci
          (congrArg Fin.castSucc hj0),
        fiveStepCornerCoeff_of_col L (Fin.castSucc j₀) (L.t1 * a) hl
          (congrArg Fin.castSucc hj0),
        mul_assoc L.t0 a L.t0, mul_assoc L.t1 a L.t0]
    · have hcj : ¬ Fin.castSucc j = Fin.castSucc j₀ :=
        fun h => hj0 (Fin.castSucc_injective n h)
      rw [fiveStepCornerCoeff_of_plain L j₀ a hi0 hj0,
        fiveStepCornerCoeff_of_plain L (Fin.castSucc j₀) (L.t0 * a) hci hcj,
        fiveStepCornerCoeff_of_plain L (Fin.castSucc j₀) (L.t1 * a) hl hcj]
  · by_cases hjr : j = r
    · have hj0 : ¬ j = j₀ := fun h => hj (h.symm.trans hjr)
      have hcj : ¬ Fin.castSucc j = Fin.castSucc j₀ :=
        fun h => hj0 (Fin.castSucc_injective n h)
      rw [LeavittFP.refineRoot_of_col L r hij a hi hjr,
        LeavittFP.refineRoot_of_col L r hij _ hi hjr, map_mul, fiveStepCornerHom_x,
        fiveStepCornerHom_x]
      by_cases hi0 : i = j₀
      · rw [fiveStepCornerCoeff_of_row L j₀ (j := j) a hi0,
          fiveStepCornerCoeff_of_row L (Fin.castSucc j₀) (j := Fin.castSucc j) (a * L.s0)
            (congrArg Fin.castSucc hi0),
          fiveStepCornerCoeff_of_row L (Fin.castSucc j₀) (j := Fin.last n) (a * L.s1)
            (congrArg Fin.castSucc hi0),
          mul_assoc L.s0 a L.s0, mul_assoc L.s0 a L.s1]
      · have hci : ¬ Fin.castSucc i = Fin.castSucc j₀ :=
          fun h => hi0 (Fin.castSucc_injective n h)
        rw [fiveStepCornerCoeff_of_plain L j₀ a hi0 hj0,
          fiveStepCornerCoeff_of_plain L (Fin.castSucc j₀) (a * L.s0) hci hcj,
          fiveStepCornerCoeff_of_plain L (Fin.castSucc j₀) (a * L.s1) hci hl]
    · rw [LeavittFP.refineRoot_of_plain L r hij a hi hjr,
        LeavittFP.refineRoot_of_plain L r hij _ hi hjr, fiveStepCornerHom_x,
        fiveStepCornerInj_coeff_castSucc]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_cornerHom_comp_refineHom

/-- Pointwise form: `σ_{castSucc j₀} (D_r v) = D_r (σ_{j₀} v)` for `j₀ ≠ r`. -/
theorem fiveStepCornerInj_cornerHom_refineHom (r j₀ : Fin n) (hj : j₀ ≠ r)
    (v : SteinbergGroup (Fin n) R) :
    fiveStepCornerHom L (Fin.castSucc j₀) (LeavittFP.refineHom L r v) =
      LeavittFP.refineHom L r (fiveStepCornerHom L j₀ v) :=
  DFunLike.congr_fun (fiveStepCornerInj_cornerHom_comp_refineHom L r j₀ hj) v

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerInj_cornerHom_refineHom

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
