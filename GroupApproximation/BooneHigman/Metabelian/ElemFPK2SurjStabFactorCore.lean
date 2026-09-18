import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabFactorPar
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, factor step: disjoint row / column conjugation (bh-met-65c)

Here `R` is an arbitrary unital ring and `L = last`.  The Steinberg core of the factor step:

* for `i ≠ j`, `x_{L,j}(b) x_{i,L}(a) x_{L,j}(-b) = x_{ij}(ab)⁻¹ x_{i,L}(a)`
  (`surjStabFactor_conj_row_single`, from `⁅x_{i,L}(a), x_{L,j}(b)⁆ = x_{ij}(ab)`);
* if `w i = 0`, then `padRow w · x_{i,L}(a) · padRow w⁻¹ = stab g · x_{i,L}(a)` for some `g`;
* if `c` and `w` have disjoint supports, then `padRow w · padCol c · padRow w⁻¹ ∈ P`
  (`surjStabFactor_conj_row_padCol_mem`).

Truth check.  Take `n = 2`, `w = (0, b)`, `c = (a, 0)`.  Then `padRow w = x_{3,2}(b)` and
`padCol c = x_{1,3}(a)`, and `x_{3,2}(b) x_{1,3}(a) x_{3,2}(-b) = x_{1,2}(-ab) x_{1,3}(a) ∈ P`.  If
the supports overlap, this fails: `x_{3,1}(b) x_{1,3}(a) x_{3,1}(-b)` changes the last row.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- `x_{L,j}(b) x_{i,L}(a) x_{L,j}(b)⁻¹ = (stab x_{ij}(ab))⁻¹ x_{i,L}(a)` for `i ≠ j`. -/
theorem surjStabFactor_conj_row_single (i j : Fin n) (hij : i ≠ j) (a b : R) :
    padRow (Pi.single j b) * padCol (Pi.single i a) * (padRow (Pi.single j b))⁻¹ =
      (stab n R (x i j hij (a * b)))⁻¹ * padCol (Pi.single i a) := by
  have hS := x_commutator (R := R) i.castSucc (Fin.last n) j.castSucc
    (Fin.castSucc_lt_last i).ne (Fin.castSucc_lt_last j).ne'
    (fun h => hij (Fin.castSucc_inj.mp h)) a b
  rw [commutatorElement_def] at hS
  rw [padRow_single, padCol_single, stab_x, ← hS]
  group

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_conj_row_single

/-- `stab x_{ij}(t)` commutes with `x_{L,k}(b)` for `k ≠ i`. -/
theorem surjStabFactor_commute_row (i j k : Fin n) (hij : i ≠ j) (hki : k ≠ i) (t b : R) :
    Commute (stab n R (x i j hij t)) (padRow (Pi.single k b)) := by
  rw [stab_x, padRow_single]
  exact x_commute_of_ne i.castSucc j.castSucc (Fin.last n) k.castSucc _ _
    (Fin.castSucc_lt_last j).ne (fun h => hki (Fin.castSucc_inj.mp h)) t b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_commute_row

/-- Partial row sums: conjugating `x_{i,L}(a)` by `padRow (Σ_{j ∈ s} w_j e_j)`, `w i = 0`. -/
theorem surjStabFactor_conj_rowSum_single (w : Fin n → R) (i : Fin n) (hw : w i = 0) (a : R)
    (s : Finset (Fin n)) :
    ∃ g : St n R, (∀ k, k ≠ i → ∀ b, Commute (stab n R g) (padRow (Pi.single k b))) ∧
      padRow (∑ j ∈ s, Pi.single j (w j)) * padCol (Pi.single i a) *
        (padRow (∑ j ∈ s, Pi.single j (w j)))⁻¹ = stab n R g * padCol (Pi.single i a) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ _ _ => by rw [map_one (stab n R)]; exact Commute.one_left _, ?_⟩
    rw [Finset.sum_empty, padRow_zero, one_mul, inv_one, mul_one, map_one (stab n R), one_mul]
  | insert j s hj ih =>
    obtain ⟨g, hg, he⟩ := ih
    rw [Finset.sum_insert hj, padRow_add, mul_inv_rev]
    by_cases hji : j = i
    · rw [hji, hw, Pi.single_zero, padRow_zero, one_mul, inv_one, mul_one]
      exact ⟨g, hg, he⟩
    · have hij : i ≠ j := fun h => hji h.symm
      refine ⟨g * (x i j hij (a * w j))⁻¹, fun k hk b' => ?_, ?_⟩
      · rw [map_mul (stab n R) g, map_inv (stab n R)]
        exact (hg k hk b').mul_left (surjStabFactor_commute_row i j k hij hk (a * w j) b').inv_left
      · calc _ = padRow (Pi.single j (w j)) *
              (padRow (∑ l ∈ s, Pi.single l (w l)) * padCol (Pi.single i a) *
                (padRow (∑ l ∈ s, Pi.single l (w l)))⁻¹) * (padRow (Pi.single j (w j)))⁻¹ := by
              simp only [mul_assoc]
          _ = padRow (Pi.single j (w j)) * (stab n R g * padCol (Pi.single i a)) *
              (padRow (Pi.single j (w j)))⁻¹ := by rw [he]
          _ = stab n R g * (padRow (Pi.single j (w j)) * padCol (Pi.single i a) *
              (padRow (Pi.single j (w j)))⁻¹) := by
              simp only [← mul_assoc]
              rw [← (hg j hji (w j)).eq]
          _ = stab n R g * ((stab n R (x i j hij (a * w j)))⁻¹ * padCol (Pi.single i a)) := by
              rw [surjStabFactor_conj_row_single i j hij a (w j)]
          _ = stab n R (g * (x i j hij (a * w j))⁻¹) * padCol (Pi.single i a) := by
              rw [map_mul (stab n R) g, map_inv (stab n R), mul_assoc]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_conj_rowSum_single

/-- If `w i = 0`, then `padRow w · x_{i,L}(a) · padRow w⁻¹ = stab g · x_{i,L}(a)`. -/
theorem surjStabFactor_conj_row_padCol_single (w : Fin n → R) (i : Fin n) (hw : w i = 0)
    (a : R) : ∃ g : St n R, padRow w * padCol (Pi.single i a) * (padRow w)⁻¹ =
      stab n R g * padCol (Pi.single i a) := by
  obtain ⟨g, -, he⟩ := surjStabFactor_conj_rowSum_single w i hw a Finset.univ
  rw [Finset.univ_sum_single w] at he
  exact ⟨g, he⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_conj_row_padCol_single
