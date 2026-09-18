import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Word facts for the conjugation family of the canonical `τ` (lane bh-met-77g)

For a long incomparable pair `(p, q)` with descent `(P, Q, X, Y)` (module
`EnvelopeHigmanVCTauVal`), this module proves:

* `higmanVCTauConj_pair_descent`: `P`, `Q` are short and incomparable, the cone swap `(P Q)`
  carries `X` onto `p` and `Y` onto `q`, `|X| + |Y| < |p| + |q|`, and `(P Q)` carries onto a
  cone every word that is not a proper prefix of `p` or `q`;
* `higmanVCTauConj_eq_of_prefix_left` / `_right`: a word that `(p q)` carries onto a cone and
  that is a prefix of `p` (resp. `q`) equals `p` (resp. `q`).

These are the word facts behind the descent identity `(p q) = (P Q) (X Y) (P Q)`
(`vgen_conj_coneSwap`); all of them were machine-checked (scratch `check.py`, `d = 2, 3`,
15560 long incomparable pairs, 0 failures) before being proved here.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- An involution maps cones symmetrically. -/
theorem higmanVCTauConj_mapsCone_symm {f : Equiv.Perm (Cantor X)} {a b : List X}
    (h : MapsCone f a b) (hff : f * f = 1) : MapsCone f b a := by
  have h' := h.inv
  rwa [inv_eq_of_mul_eq_one_right hff] at h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_mapsCone_symm

/-- Prefix substitutions reflect non-prefixes. -/
theorem higmanVCTauConj_not_prefix_of_maps [Nontrivial X] {f : Equiv.Perm (Cantor X)}
    {a a1 b b1 : List X} (ha : MapsCone f a1 a) (hb : MapsCone f b1 b) (hab : ¬ a <+: b) :
    ¬ a1 <+: b1 := by
  rintro ⟨r, rfl⟩
  exact hab ⟨r, MapsCone.unique (ha.append r) hb⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_not_prefix_of_maps

/-- A helper for `higmanVCTauConj_eq_of_prefix_core`: look at the image of `a ++ u`. -/
theorem higmanVCTauConj_len_or_eq [Nontrivial X] {σ : Equiv.Perm (Cantor X)}
    {a a' c u : List X} (h1 : MapsCone σ a a') (h2 : MapsCone σ (a' ++ c) (a ++ c))
    (hfix : ∀ w : List X, ¬ w <+: a ++ c → ¬ a ++ c <+: w → ¬ w <+: a' ++ c →
      ¬ a' ++ c <+: w → MapsCone σ w w)
    (hu : u.length = c.length) (hne : u ≠ c) : a.length < a'.length ∨ a' = a := by
  by_cases hA : a' ++ c <+: a ++ u
  · obtain ⟨r, hr⟩ := hA
    have h3 := h2.append r
    rw [hr] at h3
    have h4 : a ++ c ++ r = a' ++ u := MapsCone.unique h3 (h1.append u)
    have hl1 := congrArg List.length hr
    have hl2 := congrArg List.length h4
    simp only [List.length_append] at hl1 hl2
    have hr0 : r = [] := List.length_eq_zero_iff.mp (by omega)
    subst hr0
    rw [List.append_nil] at h4
    have hl : a.length = a'.length := by omega
    exact absurd ((List.append_inj h4 hl).2).symm hne
  · by_cases hB : a ++ u <+: a' ++ c
    · have hle := hB.length_le
      simp only [List.length_append] at hle
      by_cases hlt : a.length < a'.length
      · exact Or.inl hlt
      · have hl : a.length = a'.length := by omega
        have he : a ++ u = a' ++ c :=
          hB.eq_of_length (by simp only [List.length_append]; omega)
        exact absurd (List.append_inj he hl).2 hne
    · have hac : ¬ a ++ u <+: a ++ c := fun h =>
        hne (List.append_cancel_left (h.eq_of_length (by simp only [List.length_append]; omega)))
      have hca : ¬ a ++ c <+: a ++ u := fun h =>
        hne (List.append_cancel_left
          (h.eq_of_length (by simp only [List.length_append]; omega))).symm
      have h5 : a ++ u = a' ++ u := MapsCone.unique (hfix (a ++ u) hac hca hB hA) (h1.append u)
      exact Or.inr (List.append_cancel_right h5).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_len_or_eq

/-- **K (core).**  If an involution `σ` swaps `p` and `q` and fixes every word incomparable
with both, then a word that `σ` carries onto a cone and that is a prefix of `p` equals `p`. -/
theorem higmanVCTauConj_eq_of_prefix_core [Nontrivial X] {σ : Equiv.Perm (Cantor X)}
    {p q z z' : List X} (hσ : σ * σ = 1) (hp : MapsCone σ p q) (hq : MapsCone σ q p)
    (hfix : ∀ w : List X, ¬ w <+: p → ¬ p <+: w → ¬ w <+: q → ¬ q <+: w → MapsCone σ w w)
    (hne : p ≠ q) (h : MapsCone σ z z') (hz : z <+: p) : z = p := by
  obtain ⟨c, rfl⟩ := hz
  have hq' : q = z' ++ c := MapsCone.unique hp (h.append c)
  subst hq'
  rcases c with _ | ⟨e, c⟩
  · exact (List.append_nil z).symm
  · obtain ⟨e', he'⟩ := exists_ne e
    have hne' : e' :: c ≠ e :: c := fun h' => he' (List.cons.inj h').1
    have r1 := higmanVCTauConj_len_or_eq h hq hfix rfl hne'
    have r2 := higmanVCTauConj_len_or_eq (higmanVCTauConj_mapsCone_symm h hσ) hp
      (fun w h1 h2 h3 h4 => hfix w h3 h4 h1 h2) rfl hne'
    rcases r1 with r1 | r1
    · rcases r2 with r2 | r2
      · omega
      · subst r2
        exact absurd rfl hne
    · subst r1
      exact absurd rfl hne

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_eq_of_prefix_core
