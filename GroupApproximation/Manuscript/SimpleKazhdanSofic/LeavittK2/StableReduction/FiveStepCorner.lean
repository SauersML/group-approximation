import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementDescend
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.UsedRankFourIntertwine
import GroupApproximation.Meta.AxiomGuard

/-!
# The corner endomorphism of `St_n(R)` and the factorization `pad = D_r ∘ σ_r` (sk-leavitt-32)

Let `R` be a ring with a Leavitt family `L` (`t₀ s₀ = 1`, ...).  Fix an index `r : Fin n`.
On generators the *corner endomorphism* `σ_r : St_n(R) → St_n(R)` is

* `x_{r j}(a) ↦ x_{r j}(s₀ a)`;
* `x_{i r}(a) ↦ x_{i r}(a t₀)`;
* `xᵢⱼ(a) ↦ xᵢⱼ(a)` if `i ≠ r` and `j ≠ r`.

At the level of matrices this is `g ↦ S g T + (1 - S T)` with `S = diag(1, …, s₀, …, 1)` and
`T = diag(1, …, t₀, …, 1)`.  Only `t₀ s₀ = 1` is needed to check the Steinberg relations: the
adjacent relation through `r` in the middle reads `a t₀ · s₀ b = a b`.

The main result is the unconditional factorization
`fiveStep_refineHom_comp_cornerHom : D_r ∘ σ_r = pad_{n → n+1}`, where `D_r = refineHom L r`
is the Leavitt refinement.  So stabilization `St_n → St_{n+1}` factors through a *same-rank*
endomorphism followed by the refinement.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ}

/-- The coefficient of the corner endomorphism on the root `(i, j)`. -/
def fiveStepCornerCoeff (r i j : Fin n) (a : R) : R :=
  if i = r then L.s0 * a else if j = r then a * L.t0 else a

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerCoeff

theorem fiveStepCornerCoeff_of_row (r : Fin n) {i j : Fin n} (a : R) (hi : i = r) :
    fiveStepCornerCoeff L r i j a = L.s0 * a := by
  rw [fiveStepCornerCoeff, if_pos hi]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerCoeff_of_row

theorem fiveStepCornerCoeff_of_col (r : Fin n) {i j : Fin n} (a : R) (hi : ¬ i = r)
    (hj : j = r) : fiveStepCornerCoeff L r i j a = a * L.t0 := by
  rw [fiveStepCornerCoeff, if_neg hi, if_pos hj]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerCoeff_of_col

theorem fiveStepCornerCoeff_of_plain (r : Fin n) {i j : Fin n} (a : R) (hi : ¬ i = r)
    (hj : ¬ j = r) : fiveStepCornerCoeff L r i j a = a := by
  rw [fiveStepCornerCoeff, if_neg hi, if_neg hj]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerCoeff_of_plain

theorem fiveStepCornerCoeff_add (r i j : Fin n) (a b : R) :
    fiveStepCornerCoeff L r i j a + fiveStepCornerCoeff L r i j b =
      fiveStepCornerCoeff L r i j (a + b) := by
  by_cases hi : i = r
  · rw [fiveStepCornerCoeff_of_row L r a hi, fiveStepCornerCoeff_of_row L r b hi,
      fiveStepCornerCoeff_of_row L r (a + b) hi, mul_add]
  · by_cases hj : j = r
    · rw [fiveStepCornerCoeff_of_col L r a hi hj, fiveStepCornerCoeff_of_col L r b hi hj,
        fiveStepCornerCoeff_of_col L r (a + b) hi hj, add_mul]
    · rw [fiveStepCornerCoeff_of_plain L r a hi hj, fiveStepCornerCoeff_of_plain L r b hi hj,
        fiveStepCornerCoeff_of_plain L r (a + b) hi hj]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerCoeff_add

/-- The adjacent relation for corner coefficients.  Through `r` in the middle it is
`a t₀ · s₀ b = a b`. -/
theorem fiveStepCornerCoeff_mul (r : Fin n) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : R) :
    fiveStepCornerCoeff L r i j a * fiveStepCornerCoeff L r j k b =
      fiveStepCornerCoeff L r i k (a * b) := by
  by_cases hi : i = r
  · have hj : ¬ j = r := fun h => hij (hi.trans h.symm)
    have hk : ¬ k = r := fun h => hik (hi.trans h.symm)
    rw [fiveStepCornerCoeff_of_row L r (j := j) a hi, fiveStepCornerCoeff_of_plain L r b hj hk,
      fiveStepCornerCoeff_of_row L r (j := k) (a * b) hi, mul_assoc L.s0 a b]
  · by_cases hj : j = r
    · have hk : ¬ k = r := fun h => hjk (hj.trans h.symm)
      rw [fiveStepCornerCoeff_of_col L r a hi hj, fiveStepCornerCoeff_of_row L r (j := k) b hj,
        fiveStepCornerCoeff_of_plain L r (a * b) hi hk, mul_assoc a L.t0 (L.s0 * b),
        ← mul_assoc L.t0 L.s0 b, L.t0_s0, one_mul b]
    · by_cases hk : k = r
      · rw [fiveStepCornerCoeff_of_plain L r a hi hj, fiveStepCornerCoeff_of_col L r b hj hk,
          fiveStepCornerCoeff_of_col L r (a * b) hi hk, mul_assoc a b L.t0]
      · rw [fiveStepCornerCoeff_of_plain L r a hi hj, fiveStepCornerCoeff_of_plain L r b hj hk,
          fiveStepCornerCoeff_of_plain L r (a * b) hi hk]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCornerCoeff_mul
