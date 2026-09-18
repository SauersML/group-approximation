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
    have r1 := higmanVCTauConj_len_or_eq (u := e' :: c) h hq hfix rfl hne'
    have r2 := higmanVCTauConj_len_or_eq (u := e' :: c)
      (higmanVCTauConj_mapsCone_symm h hσ) hp
      (fun w h1 h2 h3 h4 => hfix w h3 h4 h1 h2) rfl hne'
    rcases r1 with r1 | r1
    · rcases r2 with r2 | r2
      · omega
      · subst r2
        exact absurd rfl hne
    · subst r1
      exact absurd rfl hne

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_eq_of_prefix_core

/-- **K (left).**  A word that `(p q)` carries onto a cone and that is a prefix of `p`
equals `p`. -/
theorem higmanVCTauConj_eq_of_prefix_left [Nontrivial X] {p q z z' : List X}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (hz : z <+: p) : z = p :=
  higmanVCTauConj_eq_of_prefix_core (coneSwap_mul_self hpq hqp)
    (mapsCone_coneSwap_left hpq hqp) (mapsCone_coneSwap_right hpq hqp)
    (fun _ h1 h2 h3 h4 => vgen_mapsCone_coneSwap_fix hpq hqp h1 h2 h3 h4)
    (fun e => by subst e; exact hpq (List.prefix_refl _)) h hz

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_eq_of_prefix_left

/-- **K (right).**  A word that `(p q)` carries onto a cone and that is a prefix of `q`
equals `q`. -/
theorem higmanVCTauConj_eq_of_prefix_right [Nontrivial X] {p q z z' : List X}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (hz : z <+: q) : z = q :=
  higmanVCTauConj_eq_of_prefix_core (coneSwap_mul_self hpq hqp)
    (mapsCone_coneSwap_right hpq hqp) (mapsCone_coneSwap_left hpq hqp)
    (fun _ h1 h2 h3 h4 => vgen_mapsCone_coneSwap_fix hpq hqp h3 h4 h1 h2)
    (fun e => by subst e; exact hpq (List.prefix_refl _)) h hz

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_eq_of_prefix_right

/-- The successor letter differs from `a` once `1 < d`. -/
theorem higmanVCTauConj_other_ne {d : ℕ} (hd : 1 < d) (a : Fin d) :
    higmanVCTau_other a ≠ a := by
  intro h
  have h' : (a.val + 1) % d = a.val := congrArg Fin.val h
  have ha := a.isLt
  by_cases hlt : a.val + 1 < d
  · rw [Nat.mod_eq_of_lt hlt] at h'
    omega
  · have he : a.val + 1 = d := by omega
    rw [he, Nat.mod_self] at h'
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_other_ne

/-- The facts about the short word `P := descP m o` of a main word `m` of length `≥ 4`. -/
theorem higmanVCTauConj_descP_facts {d : ℕ} (hd : 1 < d) {m o : List (Fin d)}
    (hm : 4 ≤ m.length) (hom : ¬ o <+: m) :
    (higmanVCTau_descP m o).length ≤ 2 ∧ ¬ higmanVCTau_descP m o <+: m.take 3 ∧
      ¬ m.take 3 <+: higmanVCTau_descP m o ∧
      (∀ z, z <+: higmanVCTau_descP m o → ¬ higmanVCTau_descP m o <+: z → z <+: m) ∧
      ¬ higmanVCTau_descP m o <+: o ∧ ¬ o <+: higmanVCTau_descP m o := by
  rcases m with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, t⟩⟩⟩⟩
  · simp at hm
  · simp at hm
  · simp at hm
  · simp at hm
  have hQ : (a :: b :: c :: e :: t).take 3 = [a, b, c] := rfl
  have hdesc : higmanVCTau_descP (a :: b :: c :: e :: t) o =
      if o.head? = some a then [higmanVCTau_other a] else [a, higmanVCTau_other b] := rfl
  rw [hQ, hdesc]
  by_cases ho : o.head? = some a
  · rw [if_pos ho]
    have hne := higmanVCTauConj_other_ne hd a
    refine ⟨by simp, fun h => hne (List.cons_prefix_cons.mp h).1, fun h => ?_,
      fun z hz hPz => ?_, ?_⟩
    · have hl := h.length_le
      simp at hl
    · rcases List.prefix_cons_iff.mp hz with rfl | ⟨s, rfl, hs⟩
      · exact List.nil_prefix
      · rw [List.prefix_nil.mp hs] at hPz
        exact absurd (List.prefix_refl _) hPz
    · rcases o with _ | ⟨x, o⟩
      · simp at ho
      · have hx : x = a := by simpa using ho
        subst hx
        exact ⟨fun h => hne (List.cons_prefix_cons.mp h).1,
          fun h => hne (List.cons_prefix_cons.mp h).1.symm⟩
  · rw [if_neg ho]
    have hne := higmanVCTauConj_other_ne hd b
    refine ⟨by simp, fun h => hne (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h).2).1,
      fun h => ?_, fun z hz hPz => ?_, ?_⟩
    · have hl := h.length_le
      simp at hl
    · rcases List.prefix_cons_iff.mp hz with rfl | ⟨s, rfl, hs⟩
      · exact List.nil_prefix
      · rcases List.prefix_cons_iff.mp hs with rfl | ⟨s', rfl, hs'⟩
        · exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
        · rw [List.prefix_nil.mp hs'] at hPz
          exact absurd (List.prefix_refl _) hPz
    · rcases o with _ | ⟨x, o⟩
      · exact (hom List.nil_prefix).elim
      · refine ⟨fun h => ?_, fun h => ?_⟩
        · have hx := (List.cons_prefix_cons.mp h).1
          subst hx
          exact ho rfl
        · have hx := (List.cons_prefix_cons.mp h).1
          subst hx
          exact ho rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_descP_facts

/-- **One descent step** for a main word `m` of length `≥ 4` against `o`. -/
theorem higmanVCTauConj_main_descent {d : ℕ} (hd : 1 < d) {m o : List (Fin d)}
    (hm : 4 ≤ m.length) (hom : ¬ o <+: m) :
    ∃ (hPQ : ¬ higmanVCTau_descP m o <+: m.take 3)
      (hQP : ¬ m.take 3 <+: higmanVCTau_descP m o),
      (higmanVCTau_descP m o).length ≤ 3 ∧ (m.take 3).length ≤ 3 ∧
      MapsCone (coneSwap _ _ hPQ hQP) (higmanVCTau_dM m o) m ∧
      MapsCone (coneSwap _ _ hPQ hQP) (higmanVCTau_dO m o) o ∧
      (higmanVCTau_dM m o).length < m.length ∧ (higmanVCTau_dO m o).length ≤ o.length ∧
      ∀ z, (z <+: m → z = m) → ∃ z1, MapsCone (coneSwap _ _ hPQ hQP) z z1 := by
  obtain ⟨hPl, hPQ, hQP, hPm, hPo⟩ := higmanVCTauConj_descP_facts hd hm hom
  have hQl : (m.take 3).length ≤ 3 := List.length_take_le 3 m
  have hQ3 : (m.take 3).length = 3 := List.length_take_of_le (by omega)
  refine ⟨hPQ, hQP, by omega, hQl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [higmanVCTau_dM]
    have h := (mapsCone_coneSwap_left hPQ hQP).append (m.drop 3)
    rwa [List.take_append_drop] at h
  · rw [higmanVCTau_dO]
    by_cases h : m.take 3 <+: o
    · rw [if_pos h]
      have hq : m.take 3 = o.take 3 := by
        have h' := List.prefix_iff_eq_take.mp h
        rwa [hQ3] at h'
      have ho : m.take 3 ++ o.drop 3 = o := by
        rw [hq]
        exact List.take_append_drop 3 o
      have h' := (mapsCone_coneSwap_left hPQ hQP).append (o.drop 3)
      rwa [ho] at h'
    · rw [if_neg h]
      exact vgen_mapsCone_coneSwap_fix hPQ hQP hPo.2 hPo.1
        (fun h' => hom (h'.trans (List.take_prefix 3 m))) h
  · rw [higmanVCTau_dM, List.length_append, List.length_drop]
    omega
  · rw [higmanVCTau_dO]
    by_cases h : m.take 3 <+: o
    · rw [if_pos h, List.length_append, List.length_drop]
      have hle := h.length_le
      omega
    · exact (congrArg List.length (if_neg h)).le
  · intro z hz
    by_cases h1 : higmanVCTau_descP m o <+: z
    · obtain ⟨r, rfl⟩ := h1
      exact ⟨_, (mapsCone_coneSwap_left hPQ hQP).append r⟩
    · by_cases h2 : m.take 3 <+: z
      · obtain ⟨r, rfl⟩ := h2
        exact ⟨_, (mapsCone_coneSwap_right hPQ hQP).append r⟩
      · by_cases h3 : z <+: higmanVCTau_descP m o
        · have he := congrArg List.length (hz (hPm z h3 h1))
          have hl := h3.length_le
          omega
        · by_cases h4 : z <+: m.take 3
          · have he := congrArg List.length (hz (h4.trans (List.take_prefix 3 m)))
            have hl := h4.length_le
            omega
          · exact ⟨z, vgen_mapsCone_coneSwap_fix hPQ hQP h3 h1 h4 h2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_main_descent

/-- **The descent of a long incomparable pair** `(p, q)`. -/
theorem higmanVCTauConj_pair_descent {d : ℕ} (hd : 1 < d) {p q : List (Fin d)}
    (hlong : ¬ (p.length ≤ 3 ∧ q.length ≤ 3)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) :
    ∃ (hPQ : ¬ higmanVCTau_pP (p, q) <+: higmanVCTau_pQ (p, q))
      (hQP : ¬ higmanVCTau_pQ (p, q) <+: higmanVCTau_pP (p, q)),
      (higmanVCTau_pP (p, q)).length ≤ 3 ∧ (higmanVCTau_pQ (p, q)).length ≤ 3 ∧
      MapsCone (coneSwap _ _ hPQ hQP) (higmanVCTau_pX (p, q)) p ∧
      MapsCone (coneSwap _ _ hPQ hQP) (higmanVCTau_pY (p, q)) q ∧
      (higmanVCTau_pX (p, q)).length + (higmanVCTau_pY (p, q)).length <
        p.length + q.length ∧
      ∀ z, (z <+: p → z = p) → (z <+: q → z = q) →
        ∃ z1, MapsCone (coneSwap _ _ hPQ hQP) z z1 := by
  by_cases hl : q.length ≤ p.length
  · have e1 : higmanVCTau_pP (p, q) = higmanVCTau_descP p q := if_pos hl
    have e2 : higmanVCTau_pQ (p, q) = p.take 3 := if_pos hl
    have e3 : higmanVCTau_pX (p, q) = higmanVCTau_dM p q := if_pos hl
    have e4 : higmanVCTau_pY (p, q) = higmanVCTau_dO p q := if_pos hl
    rw [e1, e2, e3, e4]
    obtain ⟨hPQ, hQP, h1, h2, h3, h4, h5, h6, h7⟩ :=
      higmanVCTauConj_main_descent hd (m := p) (o := q) (by omega) hqp
    exact ⟨hPQ, hQP, h1, h2, h3, h4, by omega, fun z hz _ => h7 z hz⟩
  · have e1 : higmanVCTau_pP (p, q) = higmanVCTau_descP q p := if_neg hl
    have e2 : higmanVCTau_pQ (p, q) = q.take 3 := if_neg hl
    have e3 : higmanVCTau_pX (p, q) = higmanVCTau_dO q p := if_neg hl
    have e4 : higmanVCTau_pY (p, q) = higmanVCTau_dM q p := if_neg hl
    rw [e1, e2, e3, e4]
    obtain ⟨hPQ, hQP, h1, h2, h3, h4, h5, h6, h7⟩ :=
      higmanVCTauConj_main_descent hd (m := q) (o := p) (by omega) hpq
    exact ⟨hPQ, hQP, h1, h2, h4, h3, by omega, fun z _ hz => h7 z hz⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_pair_descent

/-- The descent strictly decreases `|p| + |q|` on long incomparable pairs. -/
theorem higmanVCTauConj_len_lt {d : ℕ} (hd : 1 < d) {p q : List (Fin d)}
    (hlong : ¬ (p.length ≤ 3 ∧ q.length ≤ 3)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) :
    (higmanVCTau_pX (p, q)).length + (higmanVCTau_pY (p, q)).length < p.length + q.length := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := higmanVCTauConj_pair_descent hd hlong hpq hqp
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_len_lt

end GroupApproximation.BooneHigman.Metabelian.Envelope
