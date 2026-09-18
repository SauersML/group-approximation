import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabLengthEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, rank-two collapse: moves fixing index `i` (lane bh-met-89)

Here `R` is an arbitrary unital ring and `i : Fin n`.  `SurjStabCollapseFix i h` says that
`h : St_n(R)` fixes the row `e_i β` (right action through `padMat h`) and the column `e_i γ`
(left action through `padMat h⁻¹`), for all `β, γ`.  `SurjStabCollapseReach i w w'` says that
`w'` lies in the orbit of `w` under such `h`.

## What is proved

* The fixing elements are closed under products, and contain `x_{jl}(t)` for `j, l ≠ i`.
  Indeed `e_i (1 + t E_{jl}) = e_i` since `i ≠ j`, and
  `(1 - t E_{jl}) e_i = e_i` since `i ≠ l`.
* `surjStabCollapse_reach_step`: `w ↦ w + e_l (w_j t)` for distinct `j, l ≠ i`.
* The integral step and the support lemma used by the Euclid argument of
  `ElemFPK2SurjStabCollapseEuclid`.

Truth check.  These are the moves of `ElemFPK2SurjStabGaussMove`, restricted to the root
subgroups `x_{jl}` with `j, l ≠ i`.  Such a move never changes coordinate `i` of the row.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- `h` fixes the row `e_i β` and the column `e_i γ`. -/
def SurjStabCollapseFix (i : Fin n) (h : St n R) : Prop :=
  (∀ β : R, Pi.single i β ᵥ* padMat h = Pi.single i β) ∧
    ∀ γ : R, padMat h⁻¹ *ᵥ Pi.single i γ = Pi.single i γ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabCollapseFix

/-- `w'` is reached from `w` by an element fixing `e_i`. -/
def SurjStabCollapseReach (i : Fin n) (w w' : Fin n → R) : Prop :=
  ∃ h : St n R, SurjStabCollapseFix i h ∧ w ᵥ* padMat h = w'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabCollapseReach

theorem surjStabCollapse_fix_one (i : Fin n) : SurjStabCollapseFix i (1 : St n R) :=
  ⟨fun _ => by rw [map_one padMat, Matrix.vecMul_one],
    fun _ => by rw [inv_one, map_one padMat, Matrix.one_mulVec]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_fix_one

theorem surjStabCollapse_fix_mul {i : Fin n} {a b : St n R} (ha : SurjStabCollapseFix i a)
    (hb : SurjStabCollapseFix i b) : SurjStabCollapseFix i (a * b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨fun β => ?_, fun γ => ?_⟩
  · rw [map_mul padMat a b, ← Matrix.vecMul_vecMul, ha1 β, hb1 β]
  · rw [mul_inv_rev, map_mul padMat b⁻¹ a⁻¹, ← Matrix.mulVec_mulVec, ha2 γ, hb2 γ]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_fix_mul

/-- `x_{jl}(t)` with `j, l ≠ i` fixes `e_i`. -/
theorem surjStabCollapse_fix_x (i j l : Fin n) (hjl : j ≠ l) (hj : j ≠ i) (hl : l ≠ i) (t : R) :
    SurjStabCollapseFix i (x j l hjl t) := by
  refine ⟨fun β => ?_, fun γ => ?_⟩
  · rw [padMat_x]
    exact single_vecMul_one_add_single_of_ne (Ne.symm hj) β t
  · rw [← GroupApproximation.SteinbergGroup.x_neg, padMat_x]
    exact one_add_single_mulVec_single_of_ne (Ne.symm hl) (-t) γ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_fix_x

theorem surjStabCollapse_reach_refl (i : Fin n) (w : Fin n → R) :
    SurjStabCollapseReach i w w :=
  ⟨1, surjStabCollapse_fix_one i, by rw [map_one padMat, Matrix.vecMul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_reach_refl

theorem surjStabCollapse_reach_trans {i : Fin n} {w w' w'' : Fin n → R}
    (h₁ : SurjStabCollapseReach i w w') (h₂ : SurjStabCollapseReach i w' w'') :
    SurjStabCollapseReach i w w'' := by
  obtain ⟨a, ha, ha'⟩ := h₁
  obtain ⟨b, hb, hb'⟩ := h₂
  exact ⟨a * b, surjStabCollapse_fix_mul ha hb,
    by rw [map_mul padMat a b, ← Matrix.vecMul_vecMul, ha', hb']⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_reach_trans

/-- The column operation `w ↦ w + e_l (w_j t)` (`j ≠ l`, both `≠ i`) fixes `e_i`. -/
theorem surjStabCollapse_reach_step (w : Fin n → R) (i j l : Fin n) (hjl : j ≠ l) (hj : j ≠ i)
    (hl : l ≠ i) (t : R) : SurjStabCollapseReach i w (w + Pi.single l (w j * t)) :=
  ⟨x j l hjl t, surjStabCollapse_fix_x i j l hjl hj hl t,
    by rw [padMat_x, Matrix.vecMul_add, Matrix.vecMul_one, surjStab_vecMul_single]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_reach_step

/-- One integral column step on a row `s · w₀`, fixing `e_i`. -/
theorem surjStabCollapse_int_step (s : R) (w0 : Fin n → ℤ) (i j l : Fin n) (hjl : j ≠ l)
    (hj : j ≠ i) (hl : l ≠ i) (q : ℤ) :
    SurjStabCollapseReach i (fun k => s * ((w0 k : ℤ) : R))
      (fun k => s * (((w0 + Pi.single l (w0 j * q)) k : ℤ) : R)) := by
  obtain ⟨h, hf, hh⟩ :=
    surjStabCollapse_reach_step (fun k => s * ((w0 k : ℤ) : R)) i j l hjl hj hl (q : R)
  refine ⟨h, hf, hh.trans ?_⟩
  funext k
  by_cases hk : k = l
  · subst hk
    simp only [Pi.add_apply, Pi.single_eq_same, Int.cast_add, Int.cast_mul, mul_add, mul_assoc]
  · rw [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero, Pi.add_apply, Pi.single_eq_of_ne hk,
      add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_int_step

/-- If no admissible Euclid pair away from `i` exists, then away from `i` the row `w₀` is
supported at a single index `k ≠ i`. -/
theorem surjStabCollapse_int_supp (i k0 : Fin n) (hk0 : k0 ≠ i) (w0 : Fin n → ℤ)
    (hex : ¬∃ j l : Fin n, j ≠ l ∧ j ≠ i ∧ l ≠ i ∧ w0 j ≠ 0 ∧ (w0 j).natAbs ≤ (w0 l).natAbs) :
    ∃ k : Fin n, k ≠ i ∧ ∀ l, l ≠ i → l ≠ k → w0 l = 0 := by
  by_cases hall : ∃ j, j ≠ i ∧ w0 j ≠ 0
  · obtain ⟨j, hji, hj⟩ := hall
    refine ⟨j, hji, fun l hli hlj => ?_⟩
    by_contra hl0
    rcases le_total (w0 j).natAbs (w0 l).natAbs with hle | hle
    · exact hex ⟨j, l, fun e => hlj e.symm, hji, hli, hj, hle⟩
    · exact hex ⟨l, j, hlj, hli, hji, hl0, hle⟩
  · refine ⟨k0, hk0, fun l hli _ => ?_⟩
    by_contra hl0
    exact hall ⟨l, hli, hl0⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_int_supp

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
