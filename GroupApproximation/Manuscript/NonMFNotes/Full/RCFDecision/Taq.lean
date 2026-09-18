import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Chain
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.SturmTarski

/-!
# Correctness of the parametric Tarski queries and Ben-Or--Kozen--Reif sums

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  At every assignment `ρ`:

* `good_taqTree`: every true leaf of `taqTree u0 u1` carries the Tarski query
  `TaQ(Q, P)` of `P = toPoly ρ u0`, whenever `toPoly ρ u1 = P' · Q`.  The
  non-degenerate case is the Sturm--Tarski theorem `ST.taq_eq_changes` applied to
  the chain of `good_chainStart`;
* `good_bkrTree`: every true leaf of `bkrTree F us σ` carries the
  Ben-Or--Kozen--Reif sum `bkrSum`.
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

/-! ## Degenerate Tarski queries -/

theorem taq_zero_poly (Q : ℝ[X]) : taq Q 0 = 0 := by
  unfold taq
  rw [roots_zero, Multiset.toFinset_zero, Finset.sum_empty]

theorem taq_of_derivative_mul_eq_zero (P Q : ℝ[X]) (h : derivative P * Q = 0) : taq Q P = 0 := by
  rcases mul_eq_zero.1 h with hd | hQ
  · unfold taq
    rw [eq_C_of_derivative_eq_zero hd, roots_C, Multiset.toFinset_zero, Finset.sum_empty]
  · unfold taq
    exact Finset.sum_eq_zero fun _ _ => by rw [hQ, eval_zero, ST.sgn_zero]

/-! ## Tarski queries -/

/-- **Parametric Tarski query**: with `toPoly ρ u1 = P' · Q` for `P = toPoly ρ u0`,
every true leaf of `taqTree u0 u1` carries `TaQ(Q, P)`. -/
theorem good_taqTree (ρ : ℕ → ℝ) (u0 u1 : List MvP) (Q : ℝ[X])
    (hu1 : toPoly ρ u1 = derivative (toPoly ρ u0) * Q) :
    Good ρ (taqTree u0 u1) (fun z => z = taq Q (toPoly ρ u0)) := by
  unfold taqTree
  refine good_bind (good_mono (good_normUP ρ u0) ?_)
  rintro (_ | ⟨p, pl, sp⟩) ho0
  · show Good ρ (tpure (0 : ℤ)) fun z => z = taq Q (toPoly ρ u0)
    refine good_pure ρ ?_
    show (0 : ℤ) = taq Q (toPoly ρ u0)
    rw [normSpec_none] at ho0
    rw [ho0, taq_zero_poly]
  · have hP0 : toPoly ρ u0 ≠ 0 := normSpec_some_ne_zero ho0
    rw [normSpec_some] at ho0
    obtain ⟨hu0, hpl, hsp, _⟩ := ho0
    show Good ρ (tbind (normUP u1) fun o1 => o1.elim (tpure (0 : ℤ)) fun n1 =>
      tmap leafVal (chainStart p pl sp n1.1 n1.2.1 n1.2.2)) fun z => z = taq Q (toPoly ρ u0)
    refine good_bind (good_mono (good_normUP ρ u1) ?_)
    rintro (_ | ⟨q, ql, sq⟩) ho1
    · show Good ρ (tpure (0 : ℤ)) fun z => z = taq Q (toPoly ρ u0)
      refine good_pure ρ ?_
      show (0 : ℤ) = taq Q (toPoly ρ u0)
      rw [normSpec_none, hu1] at ho1
      exact (taq_of_derivative_mul_eq_zero _ _ ho1).symm
    · rw [normSpec_some] at ho1
      obtain ⟨hu1', hql, hsq, _⟩ := ho1
      have hQ' : toPoly ρ (q ++ [ql]) = derivative (toPoly ρ u0) * Q := hu1'.symm.trans hu1
      show Good ρ (tmap leafVal (chainStart p pl sp q ql sq)) fun z => z = taq Q (toPoly ρ u0)
      apply good_tmap
      refine good_mono (good_chainStart ρ p pl sp q ql sq hpl hsp hql hsq) ?_
      intro st hst
      obtain ⟨l, hne, hch, hacc⟩ := hst
      rw [hQ'] at hne
      rw [← hu0, hQ'] at hch
      rw [← hu0, hQ'] at hacc
      show ((changes (st.2.2.2.2.map Prod.snd) : ℕ) : ℤ) -
        ((changes (st.2.2.2.2.map Prod.fst) : ℕ) : ℤ) = taq Q (toPoly ρ u0)
      rw [hacc, map_snd_sgnPair, map_fst_sgnPair]
      exact (ST.taq_eq_changes (toPoly ρ u0) Q l hP0 hne hch).symm

/-! ## Products of coefficient lists -/

theorem toPoly_upOne (ρ : ℕ → ℝ) : toPoly ρ upOne = 1 := by
  show C (mvEval ρ (mvConst 1)) + X * toPoly ρ [] = 1
  rw [mvEval_const, toPoly_nil, mul_zero, add_zero, Int.cast_one, C_1]

theorem toPoly_upPow (ρ : ℕ → ℝ) (u : List MvP) : ∀ k : ℕ, toPoly ρ (upPow u k) = toPoly ρ u ^ k
  | 0 => by
      show toPoly ρ upOne = toPoly ρ u ^ 0
      rw [toPoly_upOne, pow_zero]
  | k + 1 => by
      show toPoly ρ (upMul u (upPow u k)) = toPoly ρ u ^ (k + 1)
      rw [toPoly_upMul, toPoly_upPow ρ u k, pow_succ']

theorem toPoly_prodPowUP (ρ : ℕ → ℝ) :
    ∀ (us : List (List MvP)) (e : List ℕ), toPoly ρ (prodPowUP us e) = prodPow (us.map (toPoly ρ)) e
  | [], [] => by
      show toPoly ρ upOne = 1
      exact toPoly_upOne ρ
  | [], _ :: _ => by
      show toPoly ρ upOne = 1
      exact toPoly_upOne ρ
  | _ :: _, [] => by
      show toPoly ρ upOne = 1
      exact toPoly_upOne ρ
  | u :: us, k :: e => by
      show toPoly ρ (upMul (upPow u k) (prodPowUP us e)) =
        toPoly ρ u ^ k * prodPow (us.map (toPoly ρ)) e
      rw [toPoly_upMul, toPoly_upPow, toPoly_prodPowUP ρ us e]

/-! ## Ben-Or--Kozen--Reif sums -/

theorem weightedSum_eq (σ : List ℤ) (T : List ℕ → ℤ) :
    ∀ (es : List (List ℕ)) (zs : List ℤ), AllRel (fun e z => z = T e) es zs →
      weightedSum σ es zs = (es.map fun e => weight σ e * T e).sum
  | [], [], _ => rfl
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | e :: es, z :: zs, h => by
      obtain ⟨hz, hr⟩ := h
      have hz' : z = T e := hz
      show weight σ e * z + weightedSum σ es zs =
        weight σ e * T e + (es.map fun e => weight σ e * T e).sum
      rw [hz', weightedSum_eq σ T es zs hr]

/-- **Parametric Ben-Or--Kozen--Reif sum**: every true leaf of `bkrTree F us σ`
carries `bkrSum` of the polynomials of `F` and `us` at `ρ`. -/
theorem good_bkrTree (ρ : ℕ → ℝ) (F : List MvP) (us : List (List MvP)) (σ : List ℤ) :
    Good ρ (bkrTree F us σ) (fun z => z = bkrSum (toPoly ρ F) (us.map (toPoly ρ)) σ) := by
  have ht := good_tseq ρ (fun e z => z = taq (prodPow (us.map (toPoly ρ)) e) (toPoly ρ F))
    (fun e => taqTree F (upMul (upDeriv F) (prodPowUP us e))) (expVecs us.length)
    fun e _ => good_taqTree ρ F (upMul (upDeriv F) (prodPowUP us e))
      (prodPow (us.map (toPoly ρ)) e)
      (by rw [toPoly_upMul, toPoly_upDeriv, toPoly_prodPowUP])
  unfold bkrTree
  apply good_tmap
  refine good_mono ht fun zs hzs => ?_
  show weightedSum σ (expVecs us.length) zs = bkrSum (toPoly ρ F) (us.map (toPoly ρ)) σ
  unfold bkrSum
  rw [List.length_map]
  exact weightedSum_eq σ (fun e => taq (prodPow (us.map (toPoly ρ)) e) (toPoly ρ F)) _ zs hzs

end GroupApproximation.Full.NN11b
