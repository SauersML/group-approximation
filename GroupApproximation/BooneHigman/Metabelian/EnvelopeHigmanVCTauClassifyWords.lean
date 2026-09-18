import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauUnifShape
import GroupApproximation.Meta.AxiomGuard

/-!
# Word bookkeeping for the classification over `d ≥ 3` letters (lane bh-met-78a)

With at least three letters there is always room to dodge short words: a fresh letter avoids
two given letters (`higmanVCTauClassify_fresh`), a one-letter word avoids two nonempty words
(`higmanVCTauClassify_letter`) and a two-letter word avoids two nonempty words and two words
of length at least two (`higmanVCTauClassify_avoid`).  `higmanVCTauClassify_tri` is the
trichotomy for a word under a cone swap `(p, q)`: it lies in the cone of `p`, in the cone of
`q`, or it is incomparable with both and fixed.  `higmanVCTauClassify_Good` bundles the four
flexible squares of an instance, with its two symmetries.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- With three letters, some letter differs from two given ones. -/
theorem higmanVCTauClassify_fresh {d : ℕ} (hd : 3 ≤ d) (a b : Fin d) :
    ∃ c : Fin d, c ≠ a ∧ c ≠ b := by
  have hk : ∃ k : ℕ, k < 3 ∧ k ≠ a.val ∧ k ≠ b.val := by
    by_cases h0 : 0 = a.val ∨ 0 = b.val
    · by_cases h1 : 1 = a.val ∨ 1 = b.val
      · exact ⟨2, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega⟩
  obtain ⟨k, hk3, hka, hkb⟩ := hk
  exact ⟨⟨k, by omega⟩, fun e => hka (congrArg Fin.val e), fun e => hkb (congrArg Fin.val e)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_fresh

/-- A word incomparable with something is nonempty. -/
theorem higmanVCTauClassify_ne_nil {u w : List X} (h : ¬ u <+: w) : u ≠ [] := by
  rintro rfl
  exact h List.nil_prefix

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_ne_nil

/-- A word incomparable with something has positive length. -/
theorem higmanVCTauClassify_len_pos {u w : List X} (h : ¬ u <+: w) : 0 < u.length :=
  List.length_pos_iff.mpr (higmanVCTauClassify_ne_nil h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_len_pos

/-- With three letters, some one-letter word is incomparable with two nonempty words. -/
theorem higmanVCTauClassify_letter {d : ℕ} (hd : 3 ≤ d) {p q : List (Fin d)} (hp : p ≠ [])
    (hq : q ≠ []) : ∃ c : Fin d, higmanVCTauUnif_Inc [c] p ∧ higmanVCTauUnif_Inc [c] q := by
  obtain ⟨a, p', rfl⟩ := List.exists_cons_of_ne_nil hp
  obtain ⟨b, q', rfl⟩ := List.exists_cons_of_ne_nil hq
  obtain ⟨c, hca, hcb⟩ := higmanVCTauClassify_fresh hd a b
  exact ⟨c, higmanVCTauUnif_inc_cons hca [] p', higmanVCTauUnif_inc_cons hcb [] q'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_letter

/-- A common first letter does not change incomparability. -/
theorem higmanVCTauClassify_inc_cons2 (a : X) {l l' : List X} (h : higmanVCTauUnif_Inc l l') :
    higmanVCTauUnif_Inc (a :: l) (a :: l') :=
  ⟨fun h' => h.1 (List.cons_prefix_cons.mp h').2, fun h' => h.2 (List.cons_prefix_cons.mp h').2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_inc_cons2

/-- A word of length at least two has two leading letters. -/
theorem higmanVCTauClassify_two {l : List X} (h : 2 ≤ l.length) :
    ∃ (a b : X) (l' : List X), l = a :: b :: l' := by
  rcases l with _ | ⟨a, _ | ⟨b, l'⟩⟩
  · have e : ([] : List X).length = 0 := rfl
    omega
  · have e : ([a] : List X).length = 1 := rfl
    omega
  · exact ⟨a, b, l', rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_two

/-- With three letters, some two-letter word is incomparable with two nonempty words and two
words of length at least two. -/
theorem higmanVCTauClassify_avoid {d : ℕ} (hd : 3 ≤ d) {c1 c2 c3 c4 : List (Fin d)}
    (h1 : c1 ≠ []) (h2 : c2 ≠ []) (h3 : 2 ≤ c3.length) (h4 : 2 ≤ c4.length) :
    ∃ E : List (Fin d), E.length = 2 ∧ higmanVCTauUnif_Inc E c1 ∧ higmanVCTauUnif_Inc E c2 ∧
      higmanVCTauUnif_Inc E c3 ∧ higmanVCTauUnif_Inc E c4 := by
  obtain ⟨a1, l1, rfl⟩ := List.exists_cons_of_ne_nil h1
  obtain ⟨a2, l2, rfl⟩ := List.exists_cons_of_ne_nil h2
  obtain ⟨a3, b3, l3, rfl⟩ := higmanVCTauClassify_two h3
  obtain ⟨a4, b4, l4, rfl⟩ := higmanVCTauClassify_two h4
  obtain ⟨e, he1, he2⟩ := higmanVCTauClassify_fresh hd a1 a2
  obtain ⟨f, hf3, hf4⟩ := higmanVCTauClassify_fresh hd b3 b4
  have key : ∀ (a b : Fin d) (l : List (Fin d)), f ≠ b →
      higmanVCTauUnif_Inc [e, f] (a :: b :: l) := by
    intro a b l hfb
    by_cases hea : e = a
    · rw [← hea]
      exact higmanVCTauClassify_inc_cons2 e (higmanVCTauUnif_inc_cons hfb [] l)
    · exact higmanVCTauUnif_inc_cons hea [f] (b :: l)
  exact ⟨[e, f], rfl, higmanVCTauUnif_inc_cons he1 [f] l1, higmanVCTauUnif_inc_cons he2 [f] l2,
    key a3 b3 l3 hf3, key a4 b4 l4 hf4⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_avoid

/-- A prefix `P` of `x` at least as long as `u` inherits incomparability with `u`. -/
theorem higmanVCTauClassify_inc_cut {P x u : List X} (hPx : P <+: x)
    (hl : u.length ≤ P.length) (h : higmanVCTauUnif_Inc x u) : higmanVCTauUnif_Inc P u := by
  refine ⟨fun hPu => ?_, fun huP => h.2 (huP.trans hPx)⟩
  have e : P = u := hPu.eq_of_length (Nat.le_antisymm hPu.length_le hl)
  rw [e] at hPx
  exact h.2 hPx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_inc_cut

/-- Splitting off the first letter of a suffix. -/
theorem higmanVCTauClassify_cons_eq (p : List X) (a : X) (l : List X) :
    p ++ a :: l = p ++ [a] ++ l :=
  (List.append_assoc p [a] l).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_cons_eq

/-- **Trichotomy.**  Under the swap `(p, q)` a word with an image lies in the cone of `p`, in
the cone of `q`, or is incomparable with both and fixed. -/
theorem higmanVCTauClassify_tri {d : ℕ} (hd : 1 < d) {p q x x' : List (Fin d)}
    {hpq : ¬ p <+: q} {hqp : ¬ q <+: p} (h : MapsCone (coneSwap p q hpq hqp) x x') :
    (∃ r, x = p ++ r ∧ x' = q ++ r) ∨ (∃ r, x = q ++ r ∧ x' = p ++ r) ∨
      (higmanVCTauUnif_Inc x p ∧ higmanVCTauUnif_Inc x q ∧ x' = x) := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  by_cases h1 : p <+: x
  · obtain ⟨r, rfl⟩ := h1
    exact Or.inl ⟨r, rfl, MapsCone.unique h ((mapsCone_coneSwap_left hpq hqp).append r)⟩
  by_cases h2 : q <+: x
  · obtain ⟨r, rfl⟩ := h2
    exact Or.inr (Or.inl ⟨r, rfl, MapsCone.unique h ((mapsCone_coneSwap_right hpq hqp).append r)⟩)
  have h3 : ¬ x <+: p := by
    intro hx
    have e : x = p := higmanVCTauConj_eq_of_prefix_left hpq hqp h hx
    rw [e] at h1
    exact h1 (List.prefix_refl p)
  have h4 : ¬ x <+: q := by
    intro hx
    have e : x = q := higmanVCTauConj_eq_of_prefix_right hpq hqp h hx
    rw [e] at h2
    exact h2 (List.prefix_refl q)
  exact Or.inr (Or.inr ⟨⟨h3, h1⟩, ⟨h4, h2⟩,
    MapsCone.unique h (higmanVCTauUnif_fix hpq hqp ⟨h3, h1⟩ ⟨h4, h2⟩)⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_tri

/-- Some flexible square applies to `(x, y)` or to `(x', y')`. -/
def higmanVCTauClassify_Good (d : ℕ) (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : Prop :=
  higmanVCTauComm_FlexA d p q x y hpq hqp ∨ higmanVCTauComm_FlexB d p q x y x' y' ∨
    higmanVCTauComm_FlexA d p q x' y' hpq hqp ∨ higmanVCTauComm_FlexB d p q x' y' x y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_Good

/-- `Good` is symmetric in the source and target pairs. -/
theorem higmanVCTauClassify_good_ab {d : ℕ} {p q x y x' y' : List (Fin d)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} (h : higmanVCTauClassify_Good d p q x' y' x y hpq hqp) :
    higmanVCTauClassify_Good d p q x y x' y' hpq hqp := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_good_ab

/-- `Good` is symmetric in the order of the two words of both pairs. -/
theorem higmanVCTauClassify_good_xy {d : ℕ} {p q x y x' y' : List (Fin d)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} (h : higmanVCTauClassify_Good d p q y x y' x' hpq hqp) :
    higmanVCTauClassify_Good d p q x y x' y' hpq hqp := by
  rcases h with h | h | h | h
  · exact Or.inl (higmanVCTauUnif_flexA_swap h)
  · exact Or.inr (Or.inl (higmanVCTauUnif_flexB_swap h))
  · exact Or.inr (Or.inr (Or.inl (higmanVCTauUnif_flexA_swap h)))
  · exact Or.inr (Or.inr (Or.inr (higmanVCTauUnif_flexB_swap h)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_good_xy

end GroupApproximation.BooneHigman.Metabelian.Envelope
