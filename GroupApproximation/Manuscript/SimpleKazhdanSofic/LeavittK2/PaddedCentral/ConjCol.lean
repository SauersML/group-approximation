import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.Vectors
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.MatrixId
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugating last-column vectors by padded elements (lane sk-leavitt-03)

Carto `sk-leavitt` lane 03 (Khanh Lemma 5.6), over an arbitrary unital ring `R`.
For `g : St_n(R)` and `v : R^n`:

  `stab g · padCol v · (stab g)⁻¹ = padCol (padMat g *ᵥ v)`.

We check this on generators `x_{ij}(b)`, inducting on `v` over `Pi.single`:

* `v = e_j(a)` uses `⁅x_{ij}(b), x_{j,last}(a)⁆ = x_{i,last}(b a)`;
* `v = e_p(a)` with `p ≠ j` uses the commutation of `x_{ij}` with `x_{p,last}`.

It then passes to all of `St_n(R)` by `Subgroup.closure_induction''`.
Consequently every `k ∈ K₂(n, R)` has `stab k` commuting with every `padCol v`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

open scoped Matrix commutatorElement
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

variable {R : Type*} [Ring R] {n : ℕ}

/-- Conjugating `padCol v` by the padded root `x_{ij}(b)`. -/
theorem x_conj_padCol (i j : Fin n) (hcs : i.castSucc ≠ j.castSucc) (b : R) (v : Fin n → R) :
    x i.castSucc j.castSucc hcs b * padCol v * (x i.castSucc j.castSucc hcs b)⁻¹ =
      padCol ((1 + Matrix.single i j b) *ᵥ v) := by
  induction v using Pi.single_induction with
  | zero => rw [Matrix.mulVec_zero, padCol_zero, mul_one, mul_inv_cancel]
  | add f g hf hg => rw [Matrix.mulVec_add, padCol_add, padCol_add, ← hf, ← hg]; group
  | single p a =>
    by_cases hpj : p = j
    · rw [hpj, one_add_single_mulVec_single_same, padCol_add, padCol_single j a,
        padCol_single i (b * a)]
      have hco := x_commute_of_ne i.castSucc (Fin.last n) j.castSucc (Fin.last n)
        (Fin.castSucc_lt_last i).ne (Fin.castSucc_lt_last j).ne (Fin.castSucc_lt_last j).ne'
        (Fin.castSucc_lt_last i).ne' (b * a) a
      have hcm := x_commutator i.castSucc j.castSucc (Fin.last n) hcs
        (Fin.castSucc_lt_last j).ne (Fin.castSucc_lt_last i).ne b a
      rw [← hco.eq, ← hcm, commutatorElement_def]
      group
    · have hjp : j.castSucc ≠ p.castSucc := fun e => hpj (Fin.castSucc_inj.mp e).symm
      rw [one_add_single_mulVec_single_of_ne hpj, padCol_single,
        (x_commute_of_ne i.castSucc j.castSucc p.castSucc (Fin.last n) hcs
          (Fin.castSucc_lt_last p).ne hjp (Fin.castSucc_lt_last i).ne' b a).eq,
        mul_inv_cancel_right]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.x_conj_padCol

/-- Conjugating `padCol v` by `stab x_{ij}(b)`. -/
theorem stab_x_conj_padCol (i j : Fin n) (hij : i ≠ j) (b : R) (v : Fin n → R) :
    stab n R (x i j hij b) * padCol v * (stab n R (x i j hij b))⁻¹ =
      padCol (padMat (x i j hij b) *ᵥ v) := by
  rw [stab_x, padMat_x]
  exact x_conj_padCol i j _ b v

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.stab_x_conj_padCol

/-- The multiplicative step of the closure induction for columns. -/
theorem conj_padCol_mul {g h : St n R}
    (hg : ∀ v : Fin n → R, stab n R g * padCol v * (stab n R g)⁻¹ = padCol (padMat g *ᵥ v))
    (hh : ∀ v : Fin n → R, stab n R h * padCol v * (stab n R h)⁻¹ = padCol (padMat h *ᵥ v))
    (v : Fin n → R) :
    stab n R (g * h) * padCol v * (stab n R (g * h))⁻¹ = padCol (padMat (g * h) *ᵥ v) := by
  rw [map_mul (stab n R) g h, map_mul padMat g h, ← Matrix.mulVec_mulVec,
    ← hg (padMat h *ᵥ v), ← hh v]
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.conj_padCol_mul

/-- Every element of `St_n(R)` lies in the closure of the generators. -/
theorem mem_closure_range_of (g : St n R) :
    g ∈ Subgroup.closure
      (Set.range (PresentedGroup.of : SteinbergGenerator (Fin n) R → St n R)) := by
  rw [PresentedGroup.closure_range_of]
  exact Subgroup.mem_top g

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.mem_closure_range_of

/-- **Column conjugation formula.**  `stab g · padCol v · (stab g)⁻¹ = padCol (padMat g *ᵥ v)`. -/
theorem stab_conj_padCol (g : St n R) (v : Fin n → R) :
    stab n R g * padCol v * (stab n R g)⁻¹ = padCol (padMat g *ᵥ v) := by
  have hg := mem_closure_range_of (R := R) g
  revert v
  induction hg using Subgroup.closure_induction'' with
  | mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    exact stab_x_conj_padCol i j hij b
  | inv_mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    intro v
    have e := stab_x_conj_padCol i j hij (-b) v
    rw [x_neg] at e
    exact e
  | one =>
    intro v
    simp only [map_one, Matrix.one_mulVec, one_mul, inv_one, mul_one]
  | mul g h _ _ hg hh => exact conj_padCol_mul hg hh

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.stab_conj_padCol

/-- For `k ∈ K₂(n, R)`, `stab k` commutes with every last-column vector. -/
theorem stab_commute_padCol {k : St n R} (hk : k ∈ K2 (Fin n) R) (v : Fin n → R) :
    Commute (stab n R k) (padCol v) := by
  have e := stab_conj_padCol k v
  rw [padMat_of_mem_K2 hk, Matrix.one_mulVec, mul_inv_eq_iff_eq_mul] at e
  exact e

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.stab_commute_padCol

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
