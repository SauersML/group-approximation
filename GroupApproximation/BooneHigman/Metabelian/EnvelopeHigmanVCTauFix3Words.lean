import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauRestReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Word lemmas for the both-fixed family (lane bh-met-92l)

The both-fixed family: `|p| = |q| = 3`, both `x` and `y` incomparable with `p` and with `q`
(so fixed by the cone swap `(p q)`).  Word lemmas for its form `sas` decompositions.

* `higmanVCTauFix3_avoid3`: three pairs of letters are avoided by some pair (`1 < d`);
* `higmanVCTauFix3_pairInc`: a length-2 word differing from the first two letters of a word
  is incomparable with it;
* `higmanVCTauFix3_exists_z`: a length-2 word incomparable with three words of length `≥ 2`;
* `higmanVCTauFix3_inc3`, `higmanVCTauFix3_inc3c`: the length-3 head of a word `t w` with
  `¬ p <+: t w`, `|t| = |p|`, is incomparable with `p`;
* `higmanVCTauFix3_incHead`: `e u` is incomparable with `p` when `¬ [e] <+: p`;
* `higmanVCTauFix3_split3`: a word of length `≥ 3` is `t ++ w` with `|t| = 3`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Three pairs are avoided.**  For `1 < d`, some pair of letters differs from each of three
given pairs. -/
theorem higmanVCTauFix3_avoid3 {d : ℕ} (hd : 1 < d) (a1 b1 a2 b2 a3 b3 : Fin d) :
    ∃ z0 z1 : Fin d, (z0 ≠ a1 ∨ z1 ≠ b1) ∧ (z0 ≠ a2 ∨ z1 ≠ b2) ∧ (z0 ≠ a3 ∨ z1 ≠ b3) := by
  have ho := higmanVCTauSplit_other_ne hd
  by_cases h23 : a2 = a3
  · exact ⟨higmanVCTau_other a2, higmanVCTau_other b1, Or.inr (ho b1), Or.inl (ho a2),
      Or.inl (fun h => ho a2 (h.trans h23.symm))⟩
  by_cases h12 : a1 = a2
  · by_cases hb : b1 = b2
    · exact ⟨a2, higmanVCTau_other b2, Or.inr (fun h => ho b2 (h.trans hb)), Or.inr (ho b2),
        Or.inl h23⟩
    · exact ⟨a3, higmanVCTau_other b3, Or.inl (fun h => h23 (h12.symm.trans h.symm)),
        Or.inl (fun h => h23 h.symm), Or.inr (ho b3)⟩
  · exact ⟨a2, higmanVCTau_other b2, Or.inl (Ne.symm h12), Or.inr (ho b2), Or.inl h23⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_avoid3

/-- A length-2 word differing from the first two letters of `a b u` is incomparable with it. -/
theorem higmanVCTauFix3_pairInc {d : ℕ} {z0 z1 a b : Fin d} (u : List (Fin d))
    (h : z0 ≠ a ∨ z1 ≠ b) : ¬ [z0, z1] <+: a :: b :: u ∧ ¬ a :: b :: u <+: [z0, z1] := by
  rcases h with h | h
  · exact higmanVCTauBridge_inc_cons [z1] (b :: u) h
  · by_cases h0 : z0 = a
    · subst h0
      exact higmanVCTauD2_inc2 [] u h
    · exact higmanVCTauBridge_inc_cons [z1] (b :: u) h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_pairInc

/-- **A short avoiding word.**  For `1 < d`, some length-2 word is incomparable with each of
three words of length `≥ 2`. -/
theorem higmanVCTauFix3_exists_z {d : ℕ} (hd : 1 < d) {u1 u2 u3 : List (Fin d)}
    (h1 : 2 ≤ u1.length) (h2 : 2 ≤ u2.length) (h3 : 2 ≤ u3.length) :
    ∃ z : List (Fin d), z.length = 2 ∧ (¬ z <+: u1 ∧ ¬ u1 <+: z) ∧
      (¬ z <+: u2 ∧ ¬ u2 <+: z) ∧ (¬ z <+: u3 ∧ ¬ u3 <+: z) := by
  rcases u1 with _ | ⟨a1, _ | ⟨b1, u1⟩⟩
  · simp at h1
  · simp at h1
  rcases u2 with _ | ⟨a2, _ | ⟨b2, u2⟩⟩
  · simp at h2
  · simp at h2
  rcases u3 with _ | ⟨a3, _ | ⟨b3, u3⟩⟩
  · simp at h3
  · simp at h3
  obtain ⟨z0, z1, k1, k2, k3⟩ := higmanVCTauFix3_avoid3 hd a1 b1 a2 b2 a3 b3
  exact ⟨[z0, z1], rfl, higmanVCTauFix3_pairInc u1 k1, higmanVCTauFix3_pairInc u2 k2,
    higmanVCTauFix3_pairInc u3 k3⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_exists_z

/-- The head `t` of `t w` is incomparable with `p` when `|t| = |p|` and `¬ p <+: t w`. -/
theorem higmanVCTauFix3_inc3 {d : ℕ} {p t : List (Fin d)} (w : List (Fin d))
    (ht : t.length = p.length) (h : ¬ p <+: t ++ w) : ¬ t <+: p ∧ ¬ p <+: t := by
  refine ⟨fun h' => ?_, fun h' => h (h'.trans (List.prefix_append t w))⟩
  have e := h'.eq_of_length ht
  rw [← e] at h
  exact h (List.prefix_append t w)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_inc3

/-- The head `[a b c]` of `a b c w` is incomparable with `p` when `|p| = 3` and
`¬ p <+: a b c w`. -/
theorem higmanVCTauFix3_inc3c {d : ℕ} {a b c : Fin d} {p : List (Fin d)} (w : List (Fin d))
    (hp : p.length = 3) (h : ¬ p <+: a :: b :: c :: w) : ¬ [a, b, c] <+: p ∧ ¬ p <+: [a, b, c] :=
  higmanVCTauFix3_inc3 w (by simp [hp]) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_inc3c

/-- `e u` is incomparable with a nonempty `p` when `¬ [e] <+: p`. -/
theorem higmanVCTauFix3_incHead {d : ℕ} {e : Fin d} {p : List (Fin d)} (u : List (Fin d))
    (hp : p ≠ []) (h : ¬ [e] <+: p) : ¬ e :: u <+: p ∧ ¬ p <+: e :: u := by
  rcases p with _ | ⟨a, p'⟩
  · exact absurd rfl hp
  · exact higmanVCTauBridge_inc_cons u p'
      (fun he => h (List.cons_prefix_cons.mpr ⟨he, List.nil_prefix⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_incHead

/-- A word of length `≥ 3` splits as `t ++ w` with `|t| = 3`. -/
theorem higmanVCTauFix3_split3 {d : ℕ} {x : List (Fin d)} (h : 3 ≤ x.length) :
    ∃ t w : List (Fin d), x = t ++ w ∧ t.length = 3 :=
  ⟨x.take 3, x.drop 3, (List.take_append_drop 3 x).symm, by simp only [List.length_take]; omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_split3

end GroupApproximation.BooneHigman.Metabelian.Envelope
