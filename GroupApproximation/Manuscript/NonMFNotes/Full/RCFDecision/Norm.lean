import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Algo
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.SturmTarskiParts.Local

/-!
# Correctness of sign normalization

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  The case tree `normUP u`
branches on the signs of the top coefficients of the parametric coefficient list
`u`.  At every assignment its true leaf gives the exact degree, the leading
coefficient and its sign (`good_normUP`).
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

/-! ## Branching -/

theorem sound_guardT {α : Type} {ρ : ℕ → ℝ} {g : List Atom} {t : List (List Atom × α)}
    {R : α → Prop} {l : List Atom × α} (hl : l ∈ guardT g t) (hg : guardHolds ρ l.1)
    (h : guardHolds ρ g → Good ρ t R) : R l.2 := by
  unfold guardT at hl
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
  have hg' := (guardHolds_append ρ g k.1).1 hg
  exact (h hg'.1).sound k hk hg'.2

theorem covers_guardT {α : Type} {ρ : ℕ → ℝ} {g : List Atom} {t : List (List Atom × α)}
    {R : α → Prop} (hg : guardHolds ρ g) (h : Good ρ t R) :
    ∃ l ∈ guardT g t, guardHolds ρ l.1 := by
  obtain ⟨k, hk, hgk⟩ := h.covers
  refine ⟨(g ++ k.1, k.2), ?_, (guardHolds_append ρ g k.1).2 ⟨hg, hgk⟩⟩
  unfold guardT
  exact List.mem_map.2 ⟨k, hk, rfl⟩

theorem guardHolds_pos (ρ : ℕ → ℝ) (c : MvP) : guardHolds ρ [(true, c)] ↔ 0 < mvEval ρ c :=
  (guardHolds_singleton ρ (true, c)).trans (atomHolds_true ρ c)

theorem guardHolds_neg (ρ : ℕ → ℝ) (c : MvP) :
    guardHolds ρ [(true, mvNeg c)] ↔ mvEval ρ c < 0 := by
  rw [guardHolds_singleton, atomHolds_true, mvEval_neg, neg_pos]

theorem guardHolds_zero (ρ : ℕ → ℝ) (c : MvP) : guardHolds ρ [(false, c)] ↔ mvEval ρ c = 0 :=
  (guardHolds_singleton ρ (false, c)).trans (atomHolds_false ρ c)

theorem good_branch3 {α : Type} {ρ : ℕ → ℝ} {c : MvP} {t1 t2 t3 : List (List Atom × α)}
    {R : α → Prop} (h1 : 0 < mvEval ρ c → Good ρ t1 R) (h2 : mvEval ρ c < 0 → Good ρ t2 R)
    (h3 : mvEval ρ c = 0 → Good ρ t3 R) : Good ρ (branch3 c t1 t2 t3) R := by
  constructor
  · intro l hl hg
    unfold branch3 at hl
    rcases List.mem_append.1 hl with hl' | hl'
    · rcases List.mem_append.1 hl' with hl'' | hl''
      · exact sound_guardT hl'' hg fun hg1 => h1 ((guardHolds_pos ρ c).1 hg1)
      · exact sound_guardT hl'' hg fun hg2 => h2 ((guardHolds_neg ρ c).1 hg2)
    · exact sound_guardT hl' hg fun hg3 => h3 ((guardHolds_zero ρ c).1 hg3)
  · unfold branch3
    rcases lt_trichotomy (mvEval ρ c) 0 with hc | hc | hc
    · obtain ⟨l, hl, hg⟩ := covers_guardT ((guardHolds_neg ρ c).2 hc) (h2 hc)
      exact ⟨l, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hl))), hg⟩
    · obtain ⟨l, hl, hg⟩ := covers_guardT ((guardHolds_zero ρ c).2 hc) (h3 hc)
      exact ⟨l, List.mem_append.2 (Or.inr hl), hg⟩
    · obtain ⟨l, hl, hg⟩ := covers_guardT ((guardHolds_pos ρ c).2 hc) (h1 hc)
      exact ⟨l, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hl))), hg⟩

/-! ## Normalization -/

/-- The specification of a normalization leaf for the coefficient list `u`. -/
def NormSpec (ρ : ℕ → ℝ) (u : List MvP) : Option (List MvP × MvP × Bool) → Prop
  | none => toPoly ρ u = 0
  | some (b, bl, s) => toPoly ρ u = toPoly ρ (b ++ [bl]) ∧ mvEval ρ bl ≠ 0 ∧
      sgn (mvEval ρ bl) = bsgn s ∧ b.length < u.length

theorem normSpec_none (ρ : ℕ → ℝ) (u : List MvP) : NormSpec ρ u none ↔ toPoly ρ u = 0 :=
  Iff.rfl

theorem normSpec_some (ρ : ℕ → ℝ) (u b : List MvP) (bl : MvP) (s : Bool) :
    NormSpec ρ u (some (b, bl, s)) ↔ toPoly ρ u = toPoly ρ (b ++ [bl]) ∧ mvEval ρ bl ≠ 0 ∧
      sgn (mvEval ρ bl) = bsgn s ∧ b.length < u.length :=
  Iff.rfl

theorem normSpec_top (ρ : ℕ → ℝ) (w : List MvP) (c : MvP) (s : Bool) (hc : mvEval ρ c ≠ 0)
    (hs : sgn (mvEval ρ c) = bsgn s) : NormSpec ρ (c :: w).reverse (some (w.reverse, c, s)) := by
  rw [normSpec_some, List.reverse_cons]
  refine ⟨rfl, hc, hs, ?_⟩
  rw [List.length_append, List.length_singleton]
  omega

theorem normSpec_cons_zero (ρ : ℕ → ℝ) (w : List MvP) (c : MvP) (hc : mvEval ρ c = 0) :
    ∀ o : Option (List MvP × MvP × Bool), NormSpec ρ w.reverse o → NormSpec ρ (c :: w).reverse o
  | none, ho => by
      rw [normSpec_none] at ho ⊢
      rw [List.reverse_cons, toPoly_append_single ρ c w.reverse, ho, hc, C_0, zero_mul, add_zero]
  | some (b, bl, s), ho => by
      rw [normSpec_some] at ho ⊢
      refine ⟨?_, ho.2.1, ho.2.2.1, ?_⟩
      · rw [List.reverse_cons, toPoly_append_single ρ c w.reverse, hc, C_0, zero_mul, add_zero]
        exact ho.1
      · rw [List.reverse_cons, List.length_append, List.length_singleton]
        have h4 := ho.2.2.2
        omega

theorem good_normRev (ρ : ℕ → ℝ) : ∀ w : List MvP, Good ρ (normRev w) (NormSpec ρ w.reverse)
  | [] => by
      show Good ρ (tpure none) (NormSpec ρ ([] : List MvP).reverse)
      refine good_pure ρ ?_
      rw [normSpec_none, List.reverse_nil, toPoly_nil]
  | c :: w => by
      show Good ρ (branch3 c (tpure (some (w.reverse, c, true)))
        (tpure (some (w.reverse, c, false))) (normRev w)) (NormSpec ρ (c :: w).reverse)
      apply good_branch3
      · intro hc
        exact good_pure ρ (normSpec_top ρ w c true hc.ne' (ST.sgn_of_pos hc))
      · intro hc
        exact good_pure ρ (normSpec_top ρ w c false hc.ne (ST.sgn_of_neg hc))
      · intro hc
        exact good_mono (good_normRev ρ w) (normSpec_cons_zero ρ w c hc)

/-- **Sign normalization** is a correct case tree. -/
theorem good_normUP (ρ : ℕ → ℝ) (u : List MvP) : Good ρ (normUP u) (NormSpec ρ u) := by
  have h := good_normRev ρ u.reverse
  rw [List.reverse_reverse] at h
  exact h

theorem normSpec_some_ne_zero {ρ : ℕ → ℝ} {u b : List MvP} {bl : MvP} {s : Bool}
    (h : NormSpec ρ u (some (b, bl, s))) : toPoly ρ u ≠ 0 := by
  rw [normSpec_some] at h
  rw [h.1]
  exact toPoly_append_single_ne_zero ρ b bl h.2.1

end GroupApproximation.Full.NN11b
