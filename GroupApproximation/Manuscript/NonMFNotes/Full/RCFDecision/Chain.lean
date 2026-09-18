import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Norm
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.PRem

/-!
# Correctness of the parametric Sturm chain

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  At every assignment `ρ`,
every true leaf of `chainStart p pl sp q ql sq` carries the sign list at `±∞` of a
generalized Sturm chain `P, Q', R₂, …` of nonzero polynomials, where
`P = p ++ [pl]` and `Q' = q ++ [ql]` (`good_chainStart`).

A running state `(false, v, b, bl, acc)` keeps a continuation invariant (`Cont`):
completing the chain from its last two members `A = v`, `B = b ++ [bl]` completes
the whole chain.  The length of `b` bounds the number of remaining steps.
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

noncomputable section

/-- The signs of a polynomial at `+∞` and at `-∞`. -/
def sgnPair (R : ℝ[X]) : ℤ × ℤ := (sgnTop R, sgnBot R)

theorem map_fst_sgnPair : ∀ L : List ℝ[X], (L.map sgnPair).map Prod.fst = L.map sgnTop
  | [] => rfl
  | R :: L => by
      show sgnTop R :: (L.map sgnPair).map Prod.fst = sgnTop R :: L.map sgnTop
      rw [map_fst_sgnPair L]

theorem map_snd_sgnPair : ∀ L : List ℝ[X], (L.map sgnPair).map Prod.snd = L.map sgnBot
  | [] => rfl
  | R :: L => by
      show sgnBot R :: (L.map sgnPair).map Prod.snd = sgnBot R :: L.map sgnBot
      rw [map_snd_sgnPair L]

theorem sgnPair_toPoly (ρ : ℕ → ℝ) (d : List MvP) (dl : MvP) (s : Bool) (hdl : mvEval ρ dl ≠ 0)
    (hs : sgn (mvEval ρ dl) = bsgn s) :
    sgnPair (toPoly ρ (d ++ [dl])) = (bsgn s, bsgn s * (-1) ^ d.length) := by
  unfold sgnPair sgnTop sgnBot
  rw [leadingCoeff_toPoly_append ρ d dl hdl, natDegree_toPoly_append ρ d dl hdl, ST.sgn_mul,
    ST.sgn_pow, ST.sgn_of_neg (neg_one_lt_zero : (-1 : ℝ) < 0), hs]

theorem sturmChain_pair (A B : ℝ[X]) : SturmChain [A, B] ↔ B ∣ A :=
  Iff.rfl

theorem sturmChain_cons3 (A B D : ℝ[X]) (l : List ℝ[X]) :
    SturmChain (A :: B :: D :: l) ↔ RemStep A B D ∧ SturmChain (B :: D :: l) :=
  Iff.rfl

theorem length_upNeg : ∀ u : List MvP, (upNeg u).length = u.length
  | [] => rfl
  | _ :: u => by
      show (upNeg u).length + 1 = u.length + 1
      rw [length_upNeg u]

/-! ## Invariants -/

/-- A complete chain `P, Q', l…` with sign list `acc` at `±∞`. -/
def Final (P Q' : ℝ[X]) (acc : List (ℤ × ℤ)) : Prop :=
  ∃ l : List ℝ[X], (∀ R ∈ Q' :: l, R ≠ 0) ∧ SturmChain (P :: Q' :: l) ∧
    acc = (P :: Q' :: l).map sgnPair

/-- Any completion of the chain from `A, B` completes the chain from `P, Q'`. -/
def Cont (P Q' A B : ℝ[X]) (acc : List (ℤ × ℤ)) : Prop :=
  ∀ ext : List ℝ[X], (∀ R ∈ ext, R ≠ 0) → SturmChain (A :: B :: ext) →
    Final P Q' (acc ++ ext.map sgnPair)

/-- The invariant of chain states with at most `m` remaining steps. -/
def ChainInv (ρ : ℕ → ℝ) (P Q' : ℝ[X]) (m : ℕ) :
    Bool × List MvP × List MvP × MvP × List (ℤ × ℤ) → Prop
  | (true, _, _, _, acc) => Final P Q' acc
  | (false, v, b, bl, acc) => mvEval ρ bl ≠ 0 ∧
      Cont P Q' (toPoly ρ v.reverse) (toPoly ρ (b ++ [bl])) acc ∧ b.length < m

theorem final_of_dvd {P Q' A B : ℝ[X]} {acc : List (ℤ × ℤ)} (hc : Cont P Q' A B acc)
    (h : B ∣ A) : Final P Q' acc := by
  have h2 := hc [] (fun _ hR => absurd hR List.not_mem_nil) ((sturmChain_pair A B).2 h)
  rw [List.map_nil, List.append_nil] at h2
  exact h2

/-! ## One step -/

theorem good_chainStep (ρ : ℕ → ℝ) (P Q' : ℝ[X]) (m : ℕ) :
    ∀ st : St, ChainInv ρ P Q' (m + 1) st → Good ρ (chainStep st) (ChainInv ρ P Q' m)
  | (true, v, b, bl, acc), h => by
      show Good ρ (tpure (true, v, b, bl, acc)) (ChainInv ρ P Q' m)
      exact good_pure ρ h
  | (false, v, [], bl, acc), h => by
      have h' : mvEval ρ bl ≠ 0 ∧ Cont P Q' (toPoly ρ v.reverse) (toPoly ρ ([] ++ [bl])) acc ∧
          ([] : List MvP).length < m + 1 := h
      obtain ⟨hbl, hc, _⟩ := h'
      show Good ρ (tpure (true, v, [], bl, acc)) (ChainInv ρ P Q' m)
      refine good_pure ρ ?_
      show Final P Q' acc
      refine final_of_dvd hc (Dvd.intro (C (mvEval ρ bl)⁻¹ * toPoly ρ v.reverse) ?_)
      show toPoly ρ [bl] * (C (mvEval ρ bl)⁻¹ * toPoly ρ v.reverse) = toPoly ρ v.reverse
      rw [toPoly_cons, toPoly_nil, mul_zero, add_zero, ← mul_assoc, ← C_mul,
        mul_inv_cancel₀ hbl, C_1, one_mul]
  | (false, v, c :: b, bl, acc), h => by
      have h' : mvEval ρ bl ≠ 0 ∧
          Cont P Q' (toPoly ρ v.reverse) (toPoly ρ ((c :: b) ++ [bl])) acc ∧
          (c :: b).length < m + 1 := h
      obtain ⟨hbl, hc, hm⟩ := h'
      obtain ⟨hr, c0, hc0, S, hS⟩ := premLoop_spec ρ bl (c :: b) hbl v.length v
        (Nat.le_add_right _ _)
      show Good ρ (tmap (chainNext v (c :: b) bl acc)
        (normUP (upNeg (premLoop bl (c :: b) v.length v).reverse))) (ChainInv ρ P Q' m)
      apply good_tmap
      refine good_mono (good_normUP ρ _) ?_
      rintro (_ | ⟨d, dl, s⟩) ho
      · show Final P Q' acc
        rw [normSpec_none, toPoly_upNeg, neg_eq_zero] at ho
        rw [ho, add_zero] at hS
        have h1 : C c0⁻¹ * C c0 = (1 : ℝ[X]) := by
          rw [← C_mul, inv_mul_cancel₀ hc0.ne', C_1]
        refine final_of_dvd hc (Dvd.intro (C c0⁻¹ * S) ?_)
        linear_combination toPoly ρ v.reverse * h1 - C c0⁻¹ * hS
      · rw [normSpec_some] at ho
        obtain ⟨hu, hdl, hs, hlen⟩ := ho
        rw [length_upNeg, List.length_reverse] at hlen
        have hlt : d.length < (c :: b).length := by omega
        show mvEval ρ dl ≠ 0 ∧
          Cont P Q' (toPoly ρ (bl :: (c :: b).reverse).reverse) (toPoly ρ (d ++ [dl]))
            (acc ++ [(bsgn s, bsgn s * (-1) ^ d.length)]) ∧ d.length < m
        refine ⟨hdl, ?_, by omega⟩
        intro ext hext hch
        have eA : toPoly ρ (bl :: (c :: b).reverse).reverse = toPoly ρ ((c :: b) ++ [bl]) := by
          rw [List.reverse_cons, List.reverse_reverse]
        rw [eA] at hch
        have hD : toPoly ρ (d ++ [dl]) ≠ 0 := toPoly_append_single_ne_zero ρ d dl hdl
        have hrem : RemStep (toPoly ρ v.reverse) (toPoly ρ ((c :: b) ++ [bl]))
            (toPoly ρ (d ++ [dl])) := by
          refine ⟨c0, 1, hc0, one_pos, S, ?_, ?_⟩
          · rw [C_1, one_mul, ← hu, toPoly_upNeg, sub_neg_eq_add]
            exact hS
          · apply degree_lt_degree
            rw [natDegree_toPoly_append ρ d dl hdl, natDegree_toPoly_append ρ (c :: b) bl hbl]
            exact hlt
        have h2 := hc (toPoly ρ (d ++ [dl]) :: ext) (List.forall_mem_cons.2 ⟨hD, hext⟩)
          ((sturmChain_cons3 _ _ _ ext).2 ⟨hrem, hch⟩)
        have e2 : acc ++ (toPoly ρ (d ++ [dl]) :: ext).map sgnPair =
            (acc ++ [(bsgn s, bsgn s * (-1) ^ d.length)]) ++ ext.map sgnPair := by
          rw [List.map_cons, sgnPair_toPoly ρ d dl s hdl hs, List.append_assoc,
            List.singleton_append]
        rw [e2] at h2
        exact h2

/-! ## Iteration -/

theorem good_chainIter (ρ : ℕ → ℝ) (P Q' : ℝ[X]) :
    ∀ (n m : ℕ) (t : List (List Atom × St)), Good ρ t (ChainInv ρ P Q' (m + n)) →
      Good ρ (chainIter n t) (ChainInv ρ P Q' m)
  | 0, _, _, h => h
  | n + 1, m, t, h => by
      show Good ρ (chainIter n (tbind t chainStep)) (ChainInv ρ P Q' m)
      exact good_chainIter ρ P Q' n m _
        (good_bind (good_mono h fun st hst => good_chainStep ρ P Q' (m + n) st hst))

theorem final_of_chainInv_zero (ρ : ℕ → ℝ) (P Q' : ℝ[X]) :
    ∀ st : St, ChainInv ρ P Q' 0 st → Final P Q' st.2.2.2.2
  | (true, _, _, _, _), h => h
  | (false, _, b, _, _), h => absurd (show _ ∧ _ ∧ b.length < 0 from h).2.2 (Nat.not_lt_zero _)

/-- **Parametric Sturm chain**: every true leaf of `chainStart` carries the signs at
`±∞` of a generalized Sturm chain starting with `P = p ++ [pl]`, `Q' = q ++ [ql]`. -/
theorem good_chainStart (ρ : ℕ → ℝ) (p : List MvP) (pl : MvP) (sp : Bool) (q : List MvP)
    (ql : MvP) (sq : Bool) (hpl : mvEval ρ pl ≠ 0) (hsp : sgn (mvEval ρ pl) = bsgn sp)
    (hql : mvEval ρ ql ≠ 0) (hsq : sgn (mvEval ρ ql) = bsgn sq) :
    Good ρ (chainStart p pl sp q ql sq)
      (fun st => Final (toPoly ρ (p ++ [pl])) (toPoly ρ (q ++ [ql])) st.2.2.2.2) := by
  have h0 : ChainInv ρ (toPoly ρ (p ++ [pl])) (toPoly ρ (q ++ [ql])) (0 + (q.length + 1))
      (false, pl :: p.reverse, q, ql,
        [(bsgn sp, bsgn sp * (-1) ^ p.length), (bsgn sq, bsgn sq * (-1) ^ q.length)]) := by
    rw [Nat.zero_add]
    show mvEval ρ ql ≠ 0 ∧
      Cont (toPoly ρ (p ++ [pl])) (toPoly ρ (q ++ [ql])) (toPoly ρ (pl :: p.reverse).reverse)
        (toPoly ρ (q ++ [ql]))
        [(bsgn sp, bsgn sp * (-1) ^ p.length), (bsgn sq, bsgn sq * (-1) ^ q.length)] ∧
      q.length < q.length + 1
    refine ⟨hql, ?_, Nat.lt_succ_self _⟩
    intro ext hext hch
    rw [List.reverse_cons, List.reverse_reverse] at hch
    refine ⟨ext, List.forall_mem_cons.2 ⟨toPoly_append_single_ne_zero ρ q ql hql, hext⟩, hch, ?_⟩
    rw [List.map_cons, List.map_cons, sgnPair_toPoly ρ p pl sp hpl hsp,
      sgnPair_toPoly ρ q ql sq hql hsq, List.cons_append, List.cons_append, List.nil_append]
  exact good_mono (good_chainIter ρ _ _ (q.length + 1) 0 _ (good_pure ρ h0))
    (final_of_chainInv_zero ρ _ _)

end

end GroupApproximation.Full.NN11b
