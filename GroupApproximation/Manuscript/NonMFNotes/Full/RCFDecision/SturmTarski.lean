import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.SturmTarskiParts.Cauchy

/-!
# The Sturm--Tarski theorem for generalized Sturm chains over `ℝ`

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field": the univariate step of
Tarski's decision procedure (Basu--Pollack--Roy, *Algorithms in Real Algebraic
Geometry*, Thm 2.58, via Thm 2.57 and Prop 2.55).

For `P ≠ 0` and a generalized Sturm chain `P, P' Q, R₂, …` of nonzero
polynomials (`SturmChain`, from `Univariate/Defs.lean`),
`TaQ(Q, P) = Var_{-∞} - Var_{+∞}` (`taq_eq_changes`).

Proof: `TaQ(Q, P)` is the Cauchy index `Ind(P' Q / P)` (`ST.taq_eq_cind`); the
remainder relations transport the index along the chain (`ST.cind_rel`), and each
consecutive pair contributes its sign variations at `±∞` (`ST.cind_swap`); the
last remainder divides its predecessor, so its index vanishes (`ST.cind_of_dvd`).
-/

namespace GroupApproximation.Full.NN11b

namespace ST

open Polynomial

noncomputable section

/-- Prop 2.55: at a root `x` of `P`, the jump of `P' Q / P` is `sgn Q(x)`. -/
theorem jmp_deriv (x : ℝ) {P Q : ℝ[X]} (hP : P ≠ 0) (hx : P.IsRoot x)
    (hPQ : derivative P * Q ≠ 0) : jmp x P (derivative P * Q) = sgn (Q.eval x) := by
  have hP' : derivative P ≠ 0 := left_ne_zero_of_mul hPQ
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hPQ
  obtain ⟨m, P0, hm, hPP, hP0, hl⟩ := exists_decomp x hP
  have hm0 : 0 < m := by
    rw [← hm]
    exact (rootMultiplicity_pos hP).mpr hx
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hder : derivative P =
      (X - C x) ^ j * (C ((j + 1 : ℕ) : ℝ) * P0 + (X - C x) * derivative P0) := by
    rw [hPP, derivative_mul, derivative_X_sub_C_pow, Nat.add_sub_cancel]
    ring
  have hD0 : eval x (C ((j + 1 : ℕ) : ℝ) * P0 + (X - C x) * derivative P0) =
      ((j + 1 : ℕ) : ℝ) * eval x P0 := by
    rw [eval_add, eval_mul, eval_mul, eval_C, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      add_zero]
  have hcpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hD1 : eval x (C ((j + 1 : ℕ) : ℝ) * P0 + (X - C x) * derivative P0) ≠ 0 := by
    rw [hD0]
    exact mul_ne_zero hcpos.ne' hP0
  obtain ⟨hdm, hdl⟩ := of_decomp hder hD1
  obtain ⟨k, Q0, hk, hQQ, _, hlq⟩ := exists_decomp x hQ
  obtain ⟨hmu, hlc⟩ := mu_lc0_mul x hP' hQ
  unfold jmp
  rw [hmu, hlc, hdm, hdl, hD0, hm, hl, hk, hlq]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · have hcond : j + k < j + 1 ∧ Odd (j + 1 - (j + k)) := by
      refine ⟨by omega, ?_⟩
      rw [show j + 1 - (j + k) = 1 by omega]
      exact odd_one
    rw [if_pos hcond]
    have hQe : eval x Q = eval x Q0 := by
      rw [hQQ, hk0, pow_zero, one_mul]
    rw [hQe, show eval x P0 * (((j + 1 : ℕ) : ℝ) * eval x P0 * eval x Q0) =
        ((j + 1 : ℕ) : ℝ) * (eval x P0 * eval x P0) * eval x Q0 by ring, sgn_mul,
      sgn_of_pos (mul_pos hcpos (mul_self_pos.mpr hP0)), one_mul]
  · have hcond : ¬(j + k < j + 1 ∧ Odd (j + 1 - (j + k))) := by
      intro hc
      have h1 := hc.1
      omega
    rw [if_neg hcond]
    have hQe : eval x Q = 0 := by
      rw [hQQ, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
        zero_pow (by omega : k ≠ 0), zero_mul]
    rw [hQe, sgn_zero]

/-- `TaQ(Q, P) = Ind(P' Q / P)`. -/
theorem taq_eq_cind {P Q : ℝ[X]} (hP : P ≠ 0) (hPQ : derivative P * Q ≠ 0) :
    taq Q P = cind P (derivative P * Q) := by
  unfold taq cind
  refine Finset.sum_congr rfl (fun x hx => ?_)
  exact (jmp_deriv x hP ((mem_roots hP).mp (Multiset.mem_toFinset.mp hx)) hPQ).symm

theorem changes_cons_cons (a b : ℤ) (l : List ℤ) :
    changes (a :: b :: l) = changes [a, b] + changes (b :: l) := by
  show (if a * b < 0 then 1 else 0) + changes (b :: l) =
    ((if a * b < 0 then 1 else 0) + changes [b]) + changes (b :: l)
  rw [show changes [b] = 0 from rfl, add_zero]

/-- Thm 2.58 along a chain: the Cauchy index is the difference of sign variations. -/
theorem cind_chain (l : List ℝ[X]) : ∀ A B : ℝ[X], A ≠ 0 → (∀ R ∈ B :: l, R ≠ 0) →
    SturmChain (A :: B :: l) →
      cind A B = ((changes ((A :: B :: l).map sgnBot) : ℕ) : ℤ) -
        ((changes ((A :: B :: l).map sgnTop) : ℕ) : ℤ) := by
  induction l with
  | nil =>
    intro A B hA hne hch
    have hB : B ≠ 0 := hne B List.mem_cons_self
    have hdvd : B ∣ A := hch
    have h1 := cind_swap hA hB
    have h2 := cind_of_dvd hB hA hdvd
    show cind A B = ((changes [sgnBot A, sgnBot B] : ℕ) : ℤ) -
      ((changes [sgnTop A, sgnTop B] : ℕ) : ℤ)
    linarith
  | cons D l ih =>
    intro A B hA hne hch
    have hB : B ≠ 0 := hne B List.mem_cons_self
    have hD : D ≠ 0 := hne D (List.mem_cons_of_mem B List.mem_cons_self)
    have hne' : ∀ R ∈ D :: l, R ≠ 0 := fun R hR => hne R (List.mem_cons_of_mem B hR)
    have hch2 : RemStep A B D ∧ SturmChain (B :: D :: l) := hch
    obtain ⟨⟨c, d, hc, hd, S, hrel, _⟩, hch'⟩ := hch2
    have hrel' : C c * A + C d * D = S * B := by
      rw [hrel]
      ring
    have h1 : cind B D = ((changes (sgnBot B :: (D :: l).map sgnBot) : ℕ) : ℤ) -
        ((changes (sgnTop B :: (D :: l).map sgnTop) : ℕ) : ℤ) :=
      ih B D hB hne' hch'
    have h2 := cind_swap hA hB
    have h3 := cind_rel hA hB hD hc hd hrel'
    have e1 : ((changes (sgnBot A :: sgnBot B :: (D :: l).map sgnBot) : ℕ) : ℤ) =
        ((changes [sgnBot A, sgnBot B] : ℕ) : ℤ) +
          ((changes (sgnBot B :: (D :: l).map sgnBot) : ℕ) : ℤ) := by
      rw [changes_cons_cons (sgnBot A) (sgnBot B) ((D :: l).map sgnBot), Nat.cast_add]
    have e2 : ((changes (sgnTop A :: sgnTop B :: (D :: l).map sgnTop) : ℕ) : ℤ) =
        ((changes [sgnTop A, sgnTop B] : ℕ) : ℤ) +
          ((changes (sgnTop B :: (D :: l).map sgnTop) : ℕ) : ℤ) := by
      rw [changes_cons_cons (sgnTop A) (sgnTop B) ((D :: l).map sgnTop), Nat.cast_add]
    show cind A B = ((changes (sgnBot A :: sgnBot B :: (D :: l).map sgnBot) : ℕ) : ℤ) -
      ((changes (sgnTop A :: sgnTop B :: (D :: l).map sgnTop) : ℕ) : ℤ)
    linarith

end

end ST

open Polynomial in
/-- **Sturm--Tarski** (Basu--Pollack--Roy Thm 2.58) for generalized Sturm chains:
`TaQ(Q, P) = Var_{-∞}(P, P'Q, …) - Var_{+∞}(P, P'Q, …)`.
`non_mf_group_notes.tex`, `thm:mf-arithmetic` (Tarski step). -/
theorem taq_eq_changes (P Q : ℝ[X]) (l : List ℝ[X]) (hP : P ≠ 0)
    (hne : ∀ R ∈ derivative P * Q :: l, R ≠ 0)
    (hch : SturmChain (P :: derivative P * Q :: l)) :
    taq Q P = ((changes ((P :: derivative P * Q :: l).map sgnBot) : ℕ) : ℤ) -
      ((changes ((P :: derivative P * Q :: l).map sgnTop) : ℕ) : ℤ) := by
  rw [ST.taq_eq_cind hP (hne _ List.mem_cons_self)]
  exact ST.cind_chain l P (derivative P * Q) hP hne hch

end GroupApproximation.Full.NN11b
