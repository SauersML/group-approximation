import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.ConjCol
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugating last-row vectors by padded elements (lane sk-leavitt-03)

Carto `sk-leavitt` lane 03 (Khanh Lemma 5.6), over an arbitrary unital ring `R`.
For `g : St_n(R)` and `v : R^n`:

  `(stab g)⁻¹ · padRow v · stab g = padRow (v ᵥ* padMat g)`.

We check this on generators `x_{ij}(b)`, inducting on `v` over `Pi.single`:

* `v = e_i(a)` uses `⁅x_{last,i}(a), x_{ij}(b)⁆ = x_{last,j}(a b)`;
* `v = e_p(a)` with `p ≠ i` uses the commutation of `x_{ij}` with `x_{last,p}`.

It then passes to all of `St_n(R)` by `Subgroup.closure_induction''`.
Consequently every `k ∈ K₂(n, R)` has `stab k` commuting with every `padRow v`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

open scoped Matrix commutatorElement
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

variable {R : Type*} [Ring R] {n : ℕ}

/-- Conjugating `padRow v` by the padded root `x_{ij}(b)`. -/
theorem x_conj_padRow (i j : Fin n) (hcs : i.castSucc ≠ j.castSucc) (b : R) (v : Fin n → R) :
    (x i.castSucc j.castSucc hcs b)⁻¹ * padRow v * x i.castSucc j.castSucc hcs b =
      padRow (v ᵥ* (1 + Matrix.single i j b)) := by
  induction v using Pi.single_induction with
  | zero => rw [Matrix.zero_vecMul, padRow_zero, mul_one, inv_mul_cancel]
  | add f g hf hg => rw [Matrix.add_vecMul, padRow_add, padRow_add, ← hf, ← hg]; group
  | single p a =>
    by_cases hpi : p = i
    · rw [hpi, single_vecMul_one_add_single_same, padRow_add, padRow_single i a,
        padRow_single j (a * b)]
      have hcm := x_commutator (Fin.last n) i.castSucc j.castSucc (Fin.castSucc_lt_last i).ne'
        hcs (Fin.castSucc_lt_last j).ne' a b
      have hRjR := x_commute_of_ne (Fin.last n) j.castSucc (Fin.last n) i.castSucc
        (Fin.castSucc_lt_last j).ne' (Fin.castSucc_lt_last i).ne' (Fin.castSucc_lt_last j).ne
        (Fin.castSucc_lt_last i).ne (a * b) a
      have hXRj := x_commute_of_ne i.castSucc j.castSucc (Fin.last n) j.castSucc hcs
        (Fin.castSucc_lt_last j).ne' (Fin.castSucc_lt_last j).ne hcs.symm b (a * b)
      rw [mul_assoc, inv_mul_eq_iff_eq_mul, ← hRjR.eq, ← mul_assoc, ← hXRj.eq, ← hcm,
        commutatorElement_def]
      group
    · have hpi' : p.castSucc ≠ i.castSucc := fun e => hpi (Fin.castSucc_inj.mp e)
      rw [single_vecMul_one_add_single_of_ne hpi, padRow_single, mul_assoc,
        ← (x_commute_of_ne i.castSucc j.castSucc (Fin.last n) p.castSucc hcs
          (Fin.castSucc_lt_last p).ne' (Fin.castSucc_lt_last j).ne hpi' b a).eq,
        inv_mul_cancel_left]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.x_conj_padRow

/-- Conjugating `padRow v` by `stab x_{ij}(b)`. -/
theorem stab_x_conj_padRow (i j : Fin n) (hij : i ≠ j) (b : R) (v : Fin n → R) :
    (stab n R (x i j hij b))⁻¹ * padRow v * stab n R (x i j hij b) =
      padRow (v ᵥ* padMat (x i j hij b)) := by
  rw [stab_x, padMat_x]
  exact x_conj_padRow i j _ b v

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.stab_x_conj_padRow

/-- The multiplicative step of the closure induction for rows. -/
theorem conj_padRow_mul {g h : St n R}
    (hg : ∀ v : Fin n → R, (stab n R g)⁻¹ * padRow v * stab n R g = padRow (v ᵥ* padMat g))
    (hh : ∀ v : Fin n → R, (stab n R h)⁻¹ * padRow v * stab n R h = padRow (v ᵥ* padMat h))
    (v : Fin n → R) :
    (stab n R (g * h))⁻¹ * padRow v * stab n R (g * h) = padRow (v ᵥ* padMat (g * h)) := by
  rw [map_mul (stab n R) g h, map_mul padMat g h, ← Matrix.vecMul_vecMul,
    ← hh (v ᵥ* padMat g), ← hg v]
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.conj_padRow_mul

/-- **Row conjugation formula.**  `(stab g)⁻¹ · padRow v · stab g = padRow (v ᵥ* padMat g)`. -/
theorem stab_conj_padRow (g : St n R) (v : Fin n → R) :
    (stab n R g)⁻¹ * padRow v * stab n R g = padRow (v ᵥ* padMat g) := by
  have hg := mem_closure_range_of (R := R) g
  revert v
  induction hg using Subgroup.closure_induction'' with
  | mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    exact stab_x_conj_padRow i j hij b
  | inv_mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    intro v
    have e := stab_x_conj_padRow i j hij (-b) v
    rw [x_neg] at e
    exact e
  | one =>
    intro v
    simp only [map_one, Matrix.vecMul_one, one_mul, inv_one, mul_one]
  | mul g h _ _ hg hh => exact conj_padRow_mul hg hh

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.stab_conj_padRow

/-- For `k ∈ K₂(n, R)`, `stab k` commutes with every last-row vector. -/
theorem stab_commute_padRow {k : St n R} (hk : k ∈ K2 (Fin n) R) (v : Fin n → R) :
    Commute (stab n R k) (padRow v) := by
  have e := stab_conj_padRow k v
  rw [padMat_of_mem_K2 hk, Matrix.vecMul_one, mul_assoc, inv_mul_eq_iff_eq_mul] at e
  exact e

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.stab_commute_padRow

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
