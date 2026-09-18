import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauVal
import GroupApproximation.Meta.AxiomGuard

/-!
# Word facts of the cone-swap descent (lane bh-met-77f)

For a main word `m` of length `≥ 3` and an incomparable other word `o`, with
`P := higmanVCTau_descP m o` and `Q := take 3 m` (lane bh-met-77e, module
`EnvelopeHigmanVCTauVal`), this module proves, for `1 < d`:

* `P`, `Q` are incomparable, `P` is incomparable with `o`, `|P| ≤ 2`
  (`higmanVCTauSplit_descP_facts`);
* the cone swap `(P Q)` carries the cone of `dM m o` onto `m` and the cone of `dO m o` onto `o`
  (`higmanVCTauSplit_maps_dM`, `higmanVCTauSplit_maps_dO`);
* `dM m o`, `dO m o` are incomparable, `|dM m o| < |m|`, `|dO m o| ≤ |o|`;
* **appending stability**: appending one letter `a` to both `m` and `o` leaves `P`, `Q` unchanged
  and appends `a` to `dM m o` and `dO m o`.

These were machine-checked first (`scratchpad/bh-met-77f/split_check.py`: `d = 2, 3, 4`, all
incomparable pairs of words of length `≤ 6, 5, 4` with a word of length `≥ 3`, 256520 pairs,
0 failures).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The successor letter differs from `a` once `1 < d`. -/
theorem higmanVCTauSplit_other_ne {d : ℕ} (hd : 1 < d) (a : Fin d) :
    higmanVCTau_other a ≠ a := by
  intro h
  have h' : (a.val + 1) % d = a.val := congrArg Fin.val h
  have ha := a.isLt
  rcases Nat.lt_or_ge (a.val + 1) d with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at h'
    omega
  · have he : a.val + 1 = d := by omega
    rw [he, Nat.mod_self] at h'
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_other_ne

/-- Words with different first letters are not prefixes of each other. -/
theorem higmanVCTauSplit_cons_ne {X : Type*} {x y : X} (h : x ≠ y) (xs ys : List X) :
    ¬ (x :: xs) <+: (y :: ys) :=
  fun hp => h (List.cons_prefix_cons.mp hp).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_cons_ne

/-- A word of length `≥ 3` has three first letters. -/
theorem higmanVCTauSplit_three {X : Type*} {m : List X} (hm : 3 ≤ m.length) :
    ∃ a b c : X, ∃ r : List X, m = a :: b :: c :: r := by
  match m, hm with
  | a :: b :: c :: r, _ => exact ⟨a, b, c, r, rfl⟩
  | [], h => exact absurd h (by simp)
  | [_], h => exact absurd h (by simp)
  | [_, _], h => exact absurd h (by simp)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_three

/-- A word that is not a prefix of some word is nonempty. -/
theorem higmanVCTauSplit_ne_nil {X : Type*} {m o : List X} (hom : ¬ o <+: m) :
    ∃ e : X, ∃ os : List X, o = e :: os := by
  match o, hom with
  | e :: os, _ => exact ⟨e, os, rfl⟩
  | [], h => exact absurd List.nil_prefix h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_ne_nil

/-- The defining equation of `higmanVCTau_descP` on a word with two first letters. -/
theorem higmanVCTauSplit_descP_cons {d : ℕ} (a b : Fin d) (t o : List (Fin d)) :
    higmanVCTau_descP (a :: b :: t) o =
      if o.head? = some a then [higmanVCTau_other a] else [a, higmanVCTau_other b] :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_descP_cons

/-- The short word `P` of the descent: incomparable with `Q = take 3 m` and with `o`, and of
length `≤ 2`. -/
theorem higmanVCTauSplit_descP_facts {d : ℕ} (hd : 1 < d) {m o : List (Fin d)}
    (hom : ¬ o <+: m) (hm : 3 ≤ m.length) :
    (¬ higmanVCTau_descP m o <+: m.take 3 ∧ ¬ m.take 3 <+: higmanVCTau_descP m o) ∧
      (¬ higmanVCTau_descP m o <+: o ∧ ¬ o <+: higmanVCTau_descP m o) ∧
        (higmanVCTau_descP m o).length ≤ 2 := by
  obtain ⟨a, b, c, r, rfl⟩ := higmanVCTauSplit_three hm
  obtain ⟨e, os, rfl⟩ := higmanVCTauSplit_ne_nil hom
  have hQ : (a :: b :: c :: r).take 3 = [a, b, c] := rfl
  rw [higmanVCTauSplit_descP_cons, hQ]
  have ha := higmanVCTauSplit_other_ne hd a
  have hb := higmanVCTauSplit_other_ne hd b
  split_ifs with h
  · have hea : e = a := Option.some.inj h
    have hne : higmanVCTau_other a ≠ e := by
      rw [hea]
      exact ha
    refine ⟨⟨higmanVCTauSplit_cons_ne ha _ _, higmanVCTauSplit_cons_ne (Ne.symm ha) _ _⟩,
      ⟨higmanVCTauSplit_cons_ne hne _ _, higmanVCTauSplit_cons_ne (Ne.symm hne) _ _⟩, ?_⟩
    simp
  · have hea : e ≠ a := fun h' => h (by subst h'; rfl)
    refine ⟨⟨fun hp => hb (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp hp).2).1,
      fun hp => hb (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp hp).2).1.symm⟩,
      ⟨higmanVCTauSplit_cons_ne (Ne.symm hea) _ _, higmanVCTauSplit_cons_ne hea _ _⟩, ?_⟩
    simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_descP_facts

/-- The cone swap `(P Q)` carries the cone of the descended main word onto `m`. -/
theorem higmanVCTauSplit_maps_dM {d : ℕ} {m o : List (Fin d)}
    (h1 : ¬ higmanVCTau_descP m o <+: m.take 3) (h2 : ¬ m.take 3 <+: higmanVCTau_descP m o) :
    MapsCone (coneSwap (higmanVCTau_descP m o) (m.take 3) h1 h2) (higmanVCTau_dM m o) m := by
  have h := (mapsCone_coneSwap_left h1 h2).append (m.drop 3)
  rwa [List.take_append_drop] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_maps_dM

/-- A prefix `t` of length `3` of `o` leaves `drop 3 o` as the remainder. -/
theorem higmanVCTauSplit_drop_of_prefix {X : Type*} {t o s : List X} (hs : t ++ s = o)
    (hl : t.length = 3) : o.drop 3 = s := by
  rw [← hs]
  exact List.drop_left' hl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_drop_of_prefix

/-- The cone swap `(P Q)` carries the cone of the descended other word onto `o`. -/
theorem higmanVCTauSplit_maps_dO {d : ℕ} {m o : List (Fin d)} (hom : ¬ o <+: m)
    (h1 : ¬ higmanVCTau_descP m o <+: m.take 3) (h2 : ¬ m.take 3 <+: higmanVCTau_descP m o)
    (hPo : ¬ higmanVCTau_descP m o <+: o) (hoP : ¬ o <+: higmanVCTau_descP m o)
    (hm : 3 ≤ m.length) :
    MapsCone (coneSwap (higmanVCTau_descP m o) (m.take 3) h1 h2) (higmanVCTau_dO m o) o := by
  unfold higmanVCTau_dO
  split_ifs with h
  · obtain ⟨s, hs⟩ := h
    have hl : (m.take 3).length = 3 := by
      rw [List.length_take]
      omega
    have h' := (mapsCone_coneSwap_left h1 h2).append s
    rw [hs] at h'
    rw [higmanVCTauSplit_drop_of_prefix hs hl]
    exact h'
  · exact vgen_mapsCone_coneSwap_fix h1 h2 hoP hPo
      (fun h' => hom (h'.trans (List.take_prefix 3 m))) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_maps_dO

end GroupApproximation.BooneHigman.Metabelian.Envelope
