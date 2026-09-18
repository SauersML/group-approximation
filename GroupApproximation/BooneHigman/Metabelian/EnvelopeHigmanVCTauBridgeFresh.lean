import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeChain
import Mathlib.Data.Fintype.Card
import GroupApproximation.Meta.AxiomGuard

/-!
# Fresh bridges exist on at least four letters (lane bh-met-77q)

For `d ≥ 4` every lower-level instance has a fresh one-letter word `F = [e]`
(`higmanVCTauBridge_fresh_exists`).  With `m = a b c …` the main word and `o = o₀ …` the
other word, `[e]` must avoid the first letters of `P`, `Q`, `m`, `o`, `p` and `q`:

* `Q` and `m` start with `a`; `P` starts with `a` when `o₀ ≠ a` and with `other a` when
  `o₀ = a`;
* one of `p`, `q` is a prefix of `m` or of `o` (`higmanVCTauBridge_moves`), so its first letter
  is `a` or `o₀`.

So at most three letters are forbidden (`higmanVCTauBridge_avoid3`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- On at least four letters, some letter avoids three given ones. -/
theorem higmanVCTauBridge_avoid3 {d : ℕ} (hd : 4 ≤ d) (u v w : Fin d) :
    ∃ e : Fin d, e ≠ u ∧ e ≠ v ∧ e ≠ w := by
  by_contra h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {u, v, w} := by
    intro e _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra h'
    simp only [not_or] at h'
    exact h ⟨e, h'.1, h'.2.1, h'.2.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_fin] at hc
  have h3 : ({u, v, w} : Finset (Fin d)).card ≤ 3 := Finset.card_le_three
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_avoid3

/-- A one-letter word is incomparable with any word starting with another letter. -/
theorem higmanVCTauBridge_inc_single {d : ℕ} {e c : Fin d} (W : List (Fin d)) (h : e ≠ c) :
    ¬ [e] <+: c :: W ∧ ¬ c :: W <+: [e] :=
  ⟨fun h' => h (List.cons_prefix_cons.mp h').1,
    fun h' => h (List.cons_prefix_cons.mp h').1.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_inc_single

/-- **Fresh words (main/other form).**  On at least four letters. -/
theorem higmanVCTauBridge_fresh_mo {d : ℕ} (hd4 : 4 ≤ d) {m o p q : List (Fin d)}
    (hm : 4 ≤ m.length) (hom : ¬ o <+: m) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hc : p <+: m ∨ p <+: o ∨ q <+: m ∨ q <+: o) :
    ∃ F : List (Fin d), F.length ≤ 2 ∧
      (¬ F <+: higmanVCTau_descP m o ∧ ¬ higmanVCTau_descP m o <+: F) ∧
      (¬ F <+: m.take 3 ∧ ¬ m.take 3 <+: F) ∧ (¬ F <+: m ∧ ¬ m <+: F) ∧
      (¬ F <+: o ∧ ¬ o <+: F) ∧ (¬ F <+: p ∧ ¬ p <+: F) ∧ (¬ F <+: q ∧ ¬ q <+: F) := by
  rcases m with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨k, t⟩⟩⟩⟩
  · simp at hm
  · simp at hm
  · simp at hm
  · simp at hm
  rcases o with _ | ⟨o0, o'⟩
  · exact (hom List.nil_prefix).elim
  rcases p with _ | ⟨p0, p'⟩
  · exact (hpq List.nil_prefix).elim
  rcases q with _ | ⟨q0, q'⟩
  · exact (hqp List.nil_prefix).elim
  have hkey : ∃ c' : Fin d, (p0 = a ∨ p0 = o0 ∨ p0 = c') ∧ (q0 = a ∨ q0 = o0 ∨ q0 = c') := by
    rcases hc with h | h | h | h
    · exact ⟨q0, Or.inl (List.cons_prefix_cons.mp h).1, Or.inr (Or.inr rfl)⟩
    · exact ⟨q0, Or.inr (Or.inl (List.cons_prefix_cons.mp h).1), Or.inr (Or.inr rfl)⟩
    · exact ⟨p0, Or.inr (Or.inr rfl), Or.inl (List.cons_prefix_cons.mp h).1⟩
    · exact ⟨p0, Or.inr (Or.inr rfl), Or.inr (Or.inl (List.cons_prefix_cons.mp h).1)⟩
  obtain ⟨c', hp0, hq0⟩ := hkey
  have hQ : (a :: b :: c :: k :: t).take 3 = a :: [b, c] := rfl
  have hdesc : higmanVCTau_descP (a :: b :: c :: k :: t) (o0 :: o') =
      if (o0 :: o').head? = some a then [higmanVCTau_other a]
      else [a, higmanVCTau_other b] := rfl
  rw [hQ, hdesc]
  by_cases ho : o0 = a
  · have hh : (o0 :: o').head? = some a := by rw [List.head?_cons, ho]
    rw [if_pos hh]
    obtain ⟨e, h1, h2, h3⟩ := higmanVCTauBridge_avoid3 hd4 a (higmanVCTau_other a) c'
    have heo : e ≠ o0 := by
      rw [ho]
      exact h1
    have hep : e ≠ p0 := by rcases hp0 with h | h | h <;> rw [h] <;> assumption
    have heq : e ≠ q0 := by rcases hq0 with h | h | h <;> rw [h] <;> assumption
    exact ⟨[e], by simp, higmanVCTauBridge_inc_single [] h2,
      higmanVCTauBridge_inc_single [b, c] h1, higmanVCTauBridge_inc_single _ h1,
      higmanVCTauBridge_inc_single o' heo, higmanVCTauBridge_inc_single p' hep,
      higmanVCTauBridge_inc_single q' heq⟩
  · have hh : ¬ (o0 :: o').head? = some a := by
      rw [List.head?_cons, Option.some.injEq]
      exact ho
    rw [if_neg hh]
    obtain ⟨e, h1, h2, h3⟩ := higmanVCTauBridge_avoid3 hd4 a o0 c'
    have hep : e ≠ p0 := by rcases hp0 with h | h | h <;> rw [h] <;> assumption
    have heq : e ≠ q0 := by rcases hq0 with h | h | h <;> rw [h] <;> assumption
    exact ⟨[e], by simp, higmanVCTauBridge_inc_single _ h1,
      higmanVCTauBridge_inc_single [b, c] h1, higmanVCTauBridge_inc_single _ h1,
      higmanVCTauBridge_inc_single o' h2, higmanVCTauBridge_inc_single p' hep,
      higmanVCTauBridge_inc_single q' heq⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_fresh_mo

/-- **Fresh words exist on at least four letters.** -/
theorem higmanVCTauBridge_fresh_exists {d : ℕ} (hd4 : 4 ≤ d) {p q x y x' y' : List (Fin d)}
    (hlong : ¬ (x.length ≤ 3 ∧ y.length ≤ 3)) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hlt : x'.length + y'.length < x.length + y.length) :
    ∃ F, higmanVCTauBridge_Fresh d p q x y F := by
  have hc := higmanVCTauBridge_moves (by omega) hpq hqp hmx hmy hlt
  unfold higmanVCTauBridge_Fresh
  by_cases hl : y.length ≤ x.length
  · have e1 : higmanVCTau_pP (x, y) = higmanVCTau_descP x y := if_pos hl
    have e2 : higmanVCTau_pQ (x, y) = x.take 3 := if_pos hl
    have hx4 : 4 ≤ x.length := by
      by_contra h
      exact hlong ⟨by omega, by omega⟩
    rw [e1, e2]
    obtain ⟨F, h1, h2, h3, h4, h5, h6, h7⟩ := higmanVCTauBridge_fresh_mo hd4 hx4 hyx hpq hqp hc
    exact ⟨F, h1, h2, h3, h4, h5, h6, h7⟩
  · have e1 : higmanVCTau_pP (x, y) = higmanVCTau_descP y x := if_neg hl
    have e2 : higmanVCTau_pQ (x, y) = y.take 3 := if_neg hl
    have hy4 : 4 ≤ y.length := by
      by_contra h
      exact hlong ⟨by omega, by omega⟩
    rw [e1, e2]
    have hc' : p <+: y ∨ p <+: x ∨ q <+: y ∨ q <+: x := by
      rcases hc with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    obtain ⟨F, h1, h2, h3, h4, h5, h6, h7⟩ := higmanVCTauBridge_fresh_mo hd4 hy4 hxy hpq hqp hc'
    exact ⟨F, h1, h2, h3, h5, h4, h6, h7⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_fresh_exists

end GroupApproximation.BooneHigman.Metabelian.Envelope
