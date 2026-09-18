import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeFresh
import GroupApproximation.Meta.AxiomGuard

/-!
# Helpers for fresh bridges on three letters (lane bh-met-77q)

* `higmanVCTauBridge_avoid2`: on at least three letters some letter avoids two given ones;
* `higmanVCTauBridge_inc_cons`, `higmanVCTauBridge_inc_pair`: incomparability of words that
  differ in the first, resp. second, letter;
* `higmanVCTauBridge_grow`, `higmanVCTauBridge_grow'`: a cone swap `(p q)` does not shorten a
  word lacking the longer of `p`, `q` as a prefix;
* `higmanVCTauBridge_aword_p`, `higmanVCTauBridge_aword_q`: in a level-lowering swap whose other
  word is a prefix of neither `m` nor `o`, the given word has length `≥ 2` and is a prefix of
  `m` or of `o`;
* `higmanVCTauBridge_FreshMO`: freshness in main/other form.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- On at least three letters, some letter avoids two given ones. -/
theorem higmanVCTauBridge_avoid2 {d : ℕ} (hd : 3 ≤ d) (u v : Fin d) :
    ∃ e : Fin d, e ≠ u ∧ e ≠ v := by
  by_contra h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {u, v} := by
    intro e _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra h'
    simp only [not_or] at h'
    exact h ⟨e, h'.1, h'.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_fin] at hc
  have h2 : ({u, v} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_avoid2

/-- Words with different first letters are incomparable. -/
theorem higmanVCTauBridge_inc_cons {d : ℕ} {e c : Fin d} (W1 W2 : List (Fin d)) (h : e ≠ c) :
    ¬ e :: W1 <+: c :: W2 ∧ ¬ c :: W2 <+: e :: W1 :=
  ⟨fun h' => h (List.cons_prefix_cons.mp h').1,
    fun h' => h (List.cons_prefix_cons.mp h').1.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_inc_cons

/-- A two-letter word is incomparable with a word differing from it in the second letter. -/
theorem higmanVCTauBridge_inc_pair {d : ℕ} {e z c : Fin d} (W : List (Fin d)) (h : z ≠ c) :
    ¬ [e, z] <+: e :: c :: W ∧ ¬ e :: c :: W <+: [e, z] :=
  ⟨fun h' => h (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h').2).1,
    fun h' => h (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h').2).1.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_inc_pair

/-- `(p q)` with `|p| ≤ |q|` does not shorten a word without the prefix `q`. -/
theorem higmanVCTauBridge_grow {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (hle : p.length ≤ q.length) (hqz : ¬ q <+: z) : z.length ≤ z'.length := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  by_cases h1 : p <+: z
  · obtain ⟨r, rfl⟩ := h1
    rw [MapsCone.unique h ((mapsCone_coneSwap_left hpq hqp).append r)]
    simp only [List.length_append]
    omega
  · exact (congrArg List.length (higmanVCTauBridge_eq_of_not hd hpq hqp h h1 hqz)).ge

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_grow

/-- `(p q)` with `|q| ≤ |p|` does not shorten a word without the prefix `p`. -/
theorem higmanVCTauBridge_grow' {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (hle : q.length ≤ p.length) (hpz : ¬ p <+: z) : z.length ≤ z'.length := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  by_cases h1 : q <+: z
  · obtain ⟨r, rfl⟩ := h1
    rw [MapsCone.unique h ((mapsCone_coneSwap_right hpq hqp).append r)]
    simp only [List.length_append]
    omega
  · exact (congrArg List.length (higmanVCTauBridge_eq_of_not hd hpq hqp h hpz h1)).ge

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_grow'

/-- In a level-lowering swap `(a :: p', q)` with `q` a prefix of neither `m` nor `o`, the
word `a :: p'` has length `≥ 2` and is a prefix of `m` or of `o`. -/
theorem higmanVCTauBridge_aword_p {d : ℕ} (hd : 1 < d) {a q0 : Fin d}
    {p' q' m o m' o' : List (Fin d)} (hpq : ¬ a :: p' <+: q0 :: q')
    (hqp : ¬ q0 :: q' <+: a :: p') (hsm : MapsCone (coneSwap _ _ hpq hqp) m m')
    (hso : MapsCone (coneSwap _ _ hpq hqp) o o')
    (hlt : m'.length + o'.length < m.length + o.length)
    (hqm : ¬ q0 :: q' <+: m) (hqo : ¬ q0 :: q' <+: o) :
    p' ≠ [] ∧ (a :: p' <+: m ∨ a :: p' <+: o) := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    have h1 := higmanVCTauBridge_grow hd hpq hqp hsm
      (by simp) hqm
    have h2 := higmanVCTauBridge_grow hd hpq hqp hso
      (by simp) hqo
    omega
  · rcases higmanVCTauBridge_moves hd hpq hqp hsm hso hlt with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hqm
    · exact absurd h hqo

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_aword_p

/-- In a level-lowering swap `(p, a :: q')` with `p` a prefix of neither `m` nor `o`, the
word `a :: q'` has length `≥ 2` and is a prefix of `m` or of `o`. -/
theorem higmanVCTauBridge_aword_q {d : ℕ} (hd : 1 < d) {a p0 : Fin d}
    {p' q' m o m' o' : List (Fin d)} (hpq : ¬ p0 :: p' <+: a :: q')
    (hqp : ¬ a :: q' <+: p0 :: p') (hsm : MapsCone (coneSwap _ _ hpq hqp) m m')
    (hso : MapsCone (coneSwap _ _ hpq hqp) o o')
    (hlt : m'.length + o'.length < m.length + o.length)
    (hpm : ¬ p0 :: p' <+: m) (hpo : ¬ p0 :: p' <+: o) :
    q' ≠ [] ∧ (a :: q' <+: m ∨ a :: q' <+: o) := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    have h1 := higmanVCTauBridge_grow' hd hpq hqp hsm
      (by simp) hpm
    have h2 := higmanVCTauBridge_grow' hd hpq hqp hso
      (by simp) hpo
    omega
  · rcases higmanVCTauBridge_moves hd hpq hqp hsm hso hlt with h | h | h | h
    · exact absurd h hpm
    · exact absurd h hpo
    · exact Or.inl h
    · exact Or.inr h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_aword_q

/-- Freshness in main/other form: `|F| ≤ 2` and `F` incomparable with `descP m o`,
`take 3 m`, `m`, `o`, `p`, `q`. -/
def higmanVCTauBridge_FreshMO (d : ℕ) (p q m o F : List (Fin d)) : Prop :=
  F.length ≤ 2 ∧ (¬ F <+: higmanVCTau_descP m o ∧ ¬ higmanVCTau_descP m o <+: F) ∧
    (¬ F <+: m.take 3 ∧ ¬ m.take 3 <+: F) ∧ (¬ F <+: m ∧ ¬ m <+: F) ∧
    (¬ F <+: o ∧ ¬ o <+: F) ∧ (¬ F <+: p ∧ ¬ p <+: F) ∧ (¬ F <+: q ∧ ¬ q <+: F)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_FreshMO

end GroupApproximation.BooneHigman.Metabelian.Envelope
