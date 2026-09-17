import GroupApproximation.Analysis.ExactnessPermanence
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.CoprodI

/-!
# Dykema's step, at the instance the manuscript uses

Manuscript `non_mf_group_notes.tex`, Section `sec:Esofic`, paragraph
"Exactness." (after the proof of `thm:Esofic`):

> "Each factor is finite, so it is exact, and `Q_n`, a free product of
> finitely many exact groups, is exact by Dykema's theorem \cite{DykemaExact}."

Group exactness is Yu's property A, `ExactnessPermanence.HasPropertyA`.  The
printed `Q_n` is a free product of *finitely many finite* groups, and for that
instance Dykema's theorem is proved here directly, with no citation:
`hasPropertyA_coprodI`.

Route (the tree construction).  Write `g⁻¹` in reduced normal form
`a₁ ⋯ aₘ`.  The points `(a_{j+1} ⋯ aₘ)⁻¹`, `j = 0, …, n`, walk from `g` towards
the identity along the prefixes of the normal form of `g`.  The measure at `g`
is the uniform measure on these `n + 1` points (with multiplicity).  Left
multiplication by one letter changes only the first letter of the normal form
(`Word.of_smul_def`), so it moves the measure by at most `4/(n+1)` in `ℓ¹`;
elements at distance `r` in `R` move it by at most `4L/(n+1)`, where `L` bounds
the normal-form length on `R`.  The template is the ball of radius `n`.
-/

namespace GroupApproximation.Full.NN09

open Monoid Monoid.CoprodI

universe u v

section FreeProduct

variable {ι : Type u} {M : ι → Type v} [∀ i, Group (M i)]
variable [DecidableEq ι] [∀ i, DecidableEq (M i)]

/-- The product of a list of letters in the free product. -/
def lprod (l : List (Σ i, M i)) : CoprodI M :=
  (l.map fun x => CoprodI.of x.2).prod

omit [DecidableEq ι] [∀ i, DecidableEq (M i)] in
theorem lprod_nil : lprod ([] : List (Σ i, M i)) = 1 := by
  simp [lprod]

omit [DecidableEq ι] [∀ i, DecidableEq (M i)] in
theorem lprod_cons (a : Σ i, M i) (l : List (Σ i, M i)) :
    lprod (a :: l) = CoprodI.of a.2 * lprod l := by
  simp only [lprod, List.map_cons, List.prod_cons]

omit [DecidableEq ι] [∀ i, DecidableEq (M i)] in
theorem lprod_take_mul_drop (l : List (Σ i, M i)) (j : ℕ) :
    lprod (l.take j) * lprod (l.drop j) = lprod l := by
  simp only [lprod]
  rw [← List.prod_append, ← List.map_append, List.take_append_drop]

/-- The normal form of `g`, read as a list of letters, multiplies back to `g`. -/
theorem lprod_word (g : CoprodI M) : lprod (g • (Word.empty : Word M)).toList = g := by
  change Word.prod (g • (Word.empty : Word M)) = g
  rw [Word.prod_smul, Word.prod_empty, mul_one]

/-- The `j`-th suffix point of a list of letters. -/
def pt (l : List (Σ i, M i)) (j : ℕ) : CoprodI M :=
  (lprod (l.drop j))⁻¹

omit [DecidableEq ι] [∀ i, DecidableEq (M i)] in
theorem mul_take_eq_pt {g : CoprodI M} {l : List (Σ i, M i)} (hl : lprod l = g⁻¹)
    (j : ℕ) : g * lprod (l.take j) = pt l j := by
  have h := lprod_take_mul_drop l j
  rw [hl] at h
  calc g * lprod (l.take j)
      = g * (lprod (l.take j) * lprod (l.drop j) * (lprod (l.drop j))⁻¹) := by
        rw [mul_inv_cancel_right]
    _ = g * (g⁻¹ * (lprod (l.drop j))⁻¹) := by rw [h]
    _ = (lprod (l.drop j))⁻¹ := mul_inv_cancel_left g _

/-- The counting function of the first `n` suffix points. -/
def cnt (n : ℕ) (l : List (Σ i, M i)) (x : CoprodI M) : ℝ :=
  ∑ j ∈ Finset.range n, if pt l j = x then (1 : ℝ) else 0

theorem indicator_nonneg (P : Prop) [Decidable P] : (0 : ℝ) ≤ if P then 1 else 0 := by
  split_ifs <;> norm_num

theorem sum_indicator_le (p : CoprodI M) (T : Finset (CoprodI M)) :
    ∑ x ∈ T, (if p = x then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_ite_eq]
  split_ifs <;> norm_num

theorem sum_abs_sub_triangle {α : Type*} (T : Finset α) (f g h : α → ℝ) :
    ∑ x ∈ T, |f x - h x| ≤ ∑ x ∈ T, |f x - g x| + ∑ x ∈ T, |g x - h x| := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => abs_sub_le (f x) (g x) (h x)

theorem sum_abs_sub_comm {α : Type*} (T : Finset α) (f g : α → ℝ) :
    ∑ x ∈ T, |f x - g x| = ∑ x ∈ T, |g x - f x| :=
  Finset.sum_congr rfl fun x _ => abs_sub_comm (f x) (g x)

/-- Prepending one letter moves the count by at most `2` in `ℓ¹`. -/
theorem sum_abs_cnt_cons_le (n : ℕ) (a : Σ i, M i) (l : List (Σ i, M i))
    (T : Finset (CoprodI M)) :
    ∑ x ∈ T, |cnt (n + 1) (a :: l) x - cnt (n + 1) l x| ≤ 2 := by
  have key : ∀ x, cnt (n + 1) (a :: l) x - cnt (n + 1) l x =
      (if pt (a :: l) 0 = x then (1 : ℝ) else 0) - (if pt l n = x then (1 : ℝ) else 0) := by
    intro x
    have h : ∀ i, pt (a :: l) (i + 1) = pt l i := fun _ => rfl
    simp only [cnt]
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [h]
    ring
  calc ∑ x ∈ T, |cnt (n + 1) (a :: l) x - cnt (n + 1) l x|
      ≤ ∑ x ∈ T, ((if pt (a :: l) 0 = x then (1 : ℝ) else 0) +
          (if pt l n = x then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [key x]
        have h1 := indicator_nonneg (pt (a :: l) 0 = x)
        have h2 := indicator_nonneg (pt l n = x)
        exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    _ = ∑ x ∈ T, (if pt (a :: l) 0 = x then (1 : ℝ) else 0) +
          ∑ x ∈ T, (if pt l n = x then (1 : ℝ) else 0) := Finset.sum_add_distrib
    _ ≤ 1 + 1 := add_le_add (sum_indicator_le _ _) (sum_indicator_le _ _)
    _ = 2 := by norm_num

/-- A reduced `rcons` is its tail, possibly with one letter prepended. -/
theorem sum_abs_cnt_rcons_le (n : ℕ) {i : ι} (p : Word.Pair M i) (T : Finset (CoprodI M)) :
    ∑ x ∈ T, |cnt (n + 1) (Word.rcons p).toList x - cnt (n + 1) p.tail.toList x| ≤ 2 := by
  by_cases h : p.head = 1
  · have e : (Word.rcons p).toList = p.tail.toList := by simp [Word.rcons, h]
    rw [e]
    simp only [sub_self, abs_zero, Finset.sum_const_zero]
    norm_num
  · have e : (Word.rcons p).toList = ⟨i, p.head⟩ :: p.tail.toList := by
      simp [Word.rcons, h]
    rw [e]
    exact sum_abs_cnt_cons_le n _ _ T

/-- Left multiplication by one letter moves the count by at most `4`. -/
theorem sum_abs_cnt_of_smul_le (n : ℕ) {i : ι} (m : M i) (w : Word M)
    (T : Finset (CoprodI M)) :
    ∑ x ∈ T, |cnt (n + 1) (CoprodI.of m • w).toList x - cnt (n + 1) w.toList x| ≤ 4 := by
  have hw : Word.rcons (Word.equivPair i w) = w := by
    rw [← Word.equivPair_symm, Equiv.symm_apply_apply]
  have h1 := sum_abs_cnt_rcons_le n
    (⟨m * (Word.equivPair i w).head, (Word.equivPair i w).tail,
      (Word.equivPair i w).fstIdx_ne⟩ : Word.Pair M i) T
  have h2 := sum_abs_cnt_rcons_le n (Word.equivPair i w) T
  rw [hw] at h2
  have h3 : ∑ x ∈ T, |cnt (n + 1) (Word.equivPair i w).tail.toList x -
      cnt (n + 1) w.toList x| ≤ 2 :=
    (sum_abs_sub_comm T (cnt (n + 1) (Word.equivPair i w).tail.toList)
      (cnt (n + 1) w.toList)).trans_le h2
  rw [Word.of_smul_def]
  exact (sum_abs_sub_triangle T _ (cnt (n + 1) (Word.equivPair i w).tail.toList) _).trans
    ((add_le_add h1 h3).trans (by norm_num))

/-- Left multiplication by a product of `k` letters moves the count by at most `4k`. -/
theorem sum_abs_cnt_lprod_mul_le (n : ℕ) (ls : List (Σ i, M i)) (g : CoprodI M)
    (T : Finset (CoprodI M)) :
    ∑ x ∈ T, |cnt (n + 1) ((lprod ls * g) • (Word.empty : Word M)).toList x -
      cnt (n + 1) (g • (Word.empty : Word M)).toList x| ≤ 4 * (ls.length : ℝ) := by
  induction ls with
  | nil => simp [lprod_nil]
  | cons a ls ih =>
    rw [lprod_cons, mul_assoc (CoprodI.of a.2) (lprod ls) g,
      mul_smul (CoprodI.of a.2) (lprod ls * g)]
    refine le_trans (sum_abs_sub_triangle T _
      (cnt (n + 1) ((lprod ls * g) • (Word.empty : Word M)).toList) _) ?_
    have h1 := sum_abs_cnt_of_smul_le n a.2 ((lprod ls * g) • (Word.empty : Word M)) T
    rw [List.length_cons, Nat.cast_succ]
    linarith

theorem sum_ite_mul_eq (g a : CoprodI M) (S : Finset (CoprodI M)) (ha : a ∈ S) :
    ∑ s ∈ S, (if g * a = g * s then (1 : ℝ) else 0) = 1 := by
  have hcond : ∀ s, (if g * a = g * s then (1 : ℝ) else 0) = if a = s then 1 else 0 := by
    intro s
    by_cases h : a = s
    · subst h
      simp
    · rw [if_neg h, if_neg (show ¬ g * a = g * s from fun h' => h (mul_left_cancel h'))]
  rw [Finset.sum_congr rfl fun s _ => hcond s, Finset.sum_ite_eq, if_pos ha]

variable [Fintype ι] [∀ i, Fintype (M i)]

/-- The ball of radius `n` for the word length in the letters. -/
def ball : ℕ → Finset (CoprodI M)
  | 0 => {1}
  | n + 1 => ball n ∪ (ball n ×ˢ (Finset.univ : Finset (Σ i, M i))).image
      (fun p : CoprodI M × (Σ i, M i) => CoprodI.of p.2.2 * p.1)

theorem ball_succ (n : ℕ) : ball (M := M) (n + 1) = ball n ∪
    (ball n ×ˢ (Finset.univ : Finset (Σ i, M i))).image
      (fun p : CoprodI M × (Σ i, M i) => CoprodI.of p.2.2 * p.1) := rfl

theorem one_mem_ball : ∀ n : ℕ, (1 : CoprodI M) ∈ ball n
  | 0 => Finset.mem_singleton_self 1
  | n + 1 => by
    rw [ball_succ]
    exact Finset.mem_union_left _ (one_mem_ball n)

theorem lprod_mem_ball :
    ∀ (l : List (Σ i, M i)) (n : ℕ), l.length ≤ n → lprod l ∈ ball (M := M) n
  | [], n, _ => by
    rw [lprod_nil]
    exact one_mem_ball n
  | _ :: _, 0, h => by simp at h
  | a :: l, n + 1, h => by
    have hl : l.length ≤ n := by simpa using h
    have hmem := lprod_mem_ball l n hl
    rw [lprod_cons, ball_succ]
    exact Finset.mem_union_right _ (Finset.mem_image.2
      ⟨(lprod l, a), Finset.mem_product.2 ⟨hmem, Finset.mem_univ _⟩, rfl⟩)

theorem take_mem_ball (g : CoprodI M) (n j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
    lprod ((g⁻¹ • (Word.empty : Word M)).toList.take j) ∈ ball (M := M) n :=
  lprod_mem_ball _ n
    ((List.length_take_le _ _).trans (Nat.lt_add_one_iff.1 (Finset.mem_range.1 hj)))

/-- **Dykema's step at the printed instance** (`non_mf_group_notes.tex`,
Section `sec:Esofic`, paragraph "Exactness."): a free product of finitely many
finite groups has property A (is exact). -/
theorem hasPropertyA_coprodI : ExactnessPermanence.HasPropertyA (CoprodI M) := by
  intro R ε hε
  obtain ⟨L, hLmax⟩ : ∃ L : ℕ, ∀ r ∈ R, (r⁻¹ • (Word.empty : Word M)).toList.length ≤ L :=
    ⟨_, fun r hr => Finset.le_sup
      (f := fun r : CoprodI M => (r⁻¹ • (Word.empty : Word M)).toList.length) hr⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * (L : ℝ) / ε)
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  refine ⟨{ template := ball n
            weight := fun g x =>
              ((n + 1 : ℕ) : ℝ)⁻¹ * cnt (n + 1) (g⁻¹ • (Word.empty : Word M)).toList x
            weight_nonneg := ?_
            weight_eq_zero := ?_
            weight_sum := ?_
            weight_close := ?_ }⟩
  · intro g x
    exact mul_nonneg (inv_nonneg.2 hN.le)
      (Finset.sum_nonneg fun j _ => indicator_nonneg _)
  · intro g x hx
    show ((n + 1 : ℕ) : ℝ)⁻¹ * cnt (n + 1) (g⁻¹ • (Word.empty : Word M)).toList x = 0
    have hz : cnt (n + 1) (g⁻¹ • (Word.empty : Word M)).toList x = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : ¬ pt (g⁻¹ • (Word.empty : Word M)).toList j = x := by
        intro hpt
        apply hx
        rw [← hpt, ← mul_take_eq_pt (lprod_word g⁻¹) j, inv_mul_cancel_left]
        exact take_mem_ball g n j hj
      rw [if_neg hne]
    rw [hz, mul_zero]
  · intro g
    show ∑ s ∈ ball n, ((n + 1 : ℕ) : ℝ)⁻¹ *
      cnt (n + 1) (g⁻¹ • (Word.empty : Word M)).toList (g * s) = 1
    rw [← Finset.mul_sum]
    have hj : ∀ j ∈ Finset.range (n + 1), (∑ s ∈ ball n,
        if pt (g⁻¹ • (Word.empty : Word M)).toList j = g * s then (1 : ℝ) else 0) = 1 := by
      intro j hj
      rw [← mul_take_eq_pt (lprod_word g⁻¹) j]
      exact sum_ite_mul_eq g _ (ball n) (take_mem_ball g n j hj)
    have hc : ∑ s ∈ ball n, cnt (n + 1) (g⁻¹ • (Word.empty : Word M)).toList (g * s) =
        ((n + 1 : ℕ) : ℝ) := by
      simp only [cnt]
      rw [Finset.sum_comm, Finset.sum_congr rfl hj, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
    rw [hc, inv_mul_cancel₀ hN.ne']
  · intro g h hgh T _ _
    show ∑ x ∈ T, |((n + 1 : ℕ) : ℝ)⁻¹ * cnt (n + 1) (g⁻¹ • (Word.empty : Word M)).toList x -
        ((n + 1 : ℕ) : ℝ)⁻¹ * cnt (n + 1) (h⁻¹ • (Word.empty : Word M)).toList x| ≤ ε
    have hfac : ∀ x, |((n + 1 : ℕ) : ℝ)⁻¹ * cnt (n + 1) (g⁻¹ • (Word.empty : Word M)).toList x -
        ((n + 1 : ℕ) : ℝ)⁻¹ * cnt (n + 1) (h⁻¹ • (Word.empty : Word M)).toList x| =
        ((n + 1 : ℕ) : ℝ)⁻¹ * |cnt (n + 1) (h⁻¹ • (Word.empty : Word M)).toList x -
          cnt (n + 1) (g⁻¹ • (Word.empty : Word M)).toList x| := by
      intro x
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hN), abs_sub_comm]
    rw [Finset.sum_congr rfl fun x _ => hfac x, ← Finset.mul_sum]
    have hh : h⁻¹ = lprod ((g⁻¹ * h)⁻¹ • (Word.empty : Word M)).toList * g⁻¹ := by
      rw [lprod_word]
      group
    have hD := sum_abs_cnt_lprod_mul_le n ((g⁻¹ * h)⁻¹ • (Word.empty : Word M)).toList g⁻¹ T
    rw [← hh] at hD
    have hL : ((((g⁻¹ * h)⁻¹ • (Word.empty : Word M)).toList.length : ℕ) : ℝ) ≤ (L : ℝ) :=
      Nat.cast_le.2 (hLmax _ hgh)
    have h4 : 4 * (L : ℝ) < n * ε := (div_lt_iff₀ hε).1 hn
    have h5 : 4 * (L : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * ε := by
      push_cast
      linarith
    calc ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ x ∈ T, |cnt (n + 1) (h⁻¹ • (Word.empty : Word M)).toList x -
          cnt (n + 1) (g⁻¹ • (Word.empty : Word M)).toList x|
        ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ) * ε) := by
          refine mul_le_mul_of_nonneg_left (hD.trans ?_) (inv_nonneg.2 hN.le)
          linarith
      _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]

end FreeProduct

#audit_closed_axioms GroupApproximation.Full.NN09.hasPropertyA_coprodI

end GroupApproximation.Full.NN09
