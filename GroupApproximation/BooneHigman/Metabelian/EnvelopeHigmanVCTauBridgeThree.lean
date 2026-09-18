import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeThreeWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Fresh bridges exist on at least three letters (lane bh-met-77q)

For `d ≥ 3` every lower-level instance has a fresh word `F` with `|F| ≤ 2`
(`higmanVCTauBridge_fresh_exists3`).  With main word `m = a b c k …` and other word `o = o₀ …`:

* if `o₀ = a` (so `P = [other a]` and `o = a o₁ …`): take `F = [e]`, `e ∉ {a, other a}`, when
  `p₀ = q₀ = a`; otherwise `F = [a, z]` with `z ∉ {b, o₁}`;
* if `o₀ ≠ a` (so `P = [a, other b]`): take `F = [e]`, `e ∉ {a, o₀}`, when
  `p₀, q₀ ∈ {a, o₀}`; otherwise `F = [a, z]` with `z ∉ {b, other b}`.

When `p₀ = a` in the two-letter case, `q` is a prefix of neither `m` nor `o`, so
`higmanVCTauBridge_aword_p` makes `p` a prefix of `m` or `o` of length `≥ 2`, and `F`
(incomparable with `m` and `o`) is incomparable with `p` (`higmanVCTauBridge_inc_moved`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A word incomparable with `m` and `o` is incomparable with every prefix of `m` or `o` that is
at least as long. -/
theorem higmanVCTauBridge_inc_moved {d : ℕ} {F w m o : List (Fin d)}
    (hlen : F.length ≤ w.length) (hpre : w <+: m ∨ w <+: o) (hFm : ¬ F <+: m)
    (hFo : ¬ F <+: o) : ¬ F <+: w ∧ ¬ w <+: F := by
  rcases hpre with h | h
  · refine ⟨fun h' => hFm (h'.trans h), fun h' => hFm ?_⟩
    rw [← h'.eq_of_length (le_antisymm h'.length_le hlen)]
    exact h
  · refine ⟨fun h' => hFo (h'.trans h), fun h' => hFo ?_⟩
    rw [← h'.eq_of_length (le_antisymm h'.length_le hlen)]
    exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_inc_moved

/-- A two-letter word is not longer than `u :: W` with `W ≠ []`. -/
theorem higmanVCTauBridge_two_le {d : ℕ} {u e z : Fin d} {W : List (Fin d)} (h : W ≠ []) :
    [e, z].length ≤ (u :: W).length := by
  rcases W with _ | ⟨v, W⟩
  · exact absurd rfl h
  · simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_two_le

/-- **Fresh words, `o₀ = a`.** -/
theorem higmanVCTauBridge_three_eq {d : ℕ} (hd3 : 3 ≤ d) {a b c k o0 o1 p0 q0 : Fin d}
    {t o'' p' q' m' o2 : List (Fin d)} (ho : o0 = a)
    (hpq : ¬ p0 :: p' <+: q0 :: q') (hqp : ¬ q0 :: q' <+: p0 :: p')
    (hsm : MapsCone (coneSwap _ _ hpq hqp) (a :: b :: c :: k :: t) m')
    (hso : MapsCone (coneSwap _ _ hpq hqp) (o0 :: o1 :: o'') o2)
    (hlt : m'.length + o2.length <
      (a :: b :: c :: k :: t).length + (o0 :: o1 :: o'').length) :
    ∃ F, higmanVCTauBridge_FreshMO d (p0 :: p') (q0 :: q') (a :: b :: c :: k :: t)
      (o0 :: o1 :: o'') F := by
  have hd : 1 < d := by omega
  unfold higmanVCTauBridge_FreshMO
  have hQ : (a :: b :: c :: k :: t).take 3 = a :: [b, c] := rfl
  have hdesc : higmanVCTau_descP (a :: b :: c :: k :: t) (o0 :: o1 :: o'') =
      if (o0 :: o1 :: o'').head? = some a then [higmanVCTau_other a]
      else [a, higmanVCTau_other b] := rfl
  have hh : (o0 :: o1 :: o'').head? = some a := by rw [List.head?_cons, ho]
  rw [hQ, hdesc, if_pos hh]
  by_cases hbad : p0 = a ∧ q0 = a
  · obtain ⟨e, h1, h2⟩ := higmanVCTauBridge_avoid2 hd3 a (higmanVCTau_other a)
    have heo : e ≠ o0 := by
      rw [ho]
      exact h1
    have hep : e ≠ p0 := by
      rw [hbad.1]
      exact h1
    have heq : e ≠ q0 := by
      rw [hbad.2]
      exact h1
    exact ⟨[e], by simp, higmanVCTauBridge_inc_single [] h2,
      higmanVCTauBridge_inc_single [b, c] h1, higmanVCTauBridge_inc_single _ h1,
      higmanVCTauBridge_inc_single (o1 :: o'') heo, higmanVCTauBridge_inc_single p' hep,
      higmanVCTauBridge_inc_single q' heq⟩
  · obtain ⟨z, hzb, hzo⟩ := higmanVCTauBridge_avoid2 hd3 b o1
    have hFm : ¬ [a, z] <+: a :: b :: c :: k :: t ∧ ¬ a :: b :: c :: k :: t <+: [a, z] :=
      higmanVCTauBridge_inc_pair _ hzb
    have hFo : ¬ [a, z] <+: o0 :: o1 :: o'' ∧ ¬ o0 :: o1 :: o'' <+: [a, z] := by
      rw [ho]
      exact higmanVCTauBridge_inc_pair o'' hzo
    have hp_ok : ¬ [a, z] <+: p0 :: p' ∧ ¬ p0 :: p' <+: [a, z] := by
      by_cases hpa : p0 = a
      · have hqa : q0 ≠ a := fun h => hbad ⟨hpa, h⟩
        have hqo : ¬ q0 :: q' <+: o0 :: o1 :: o'' := by
          rw [ho]
          exact (higmanVCTauBridge_inc_cons q' (o1 :: o'') hqa).1
        obtain ⟨hne, hpre⟩ := higmanVCTauBridge_aword_p hd hpq hqp hsm hso hlt
          (higmanVCTauBridge_inc_cons q' _ hqa).1 hqo
        exact higmanVCTauBridge_inc_moved (higmanVCTauBridge_two_le hne) hpre hFm.1 hFo.1
      · exact higmanVCTauBridge_inc_cons [z] p' (fun h => hpa h.symm)
    have hq_ok : ¬ [a, z] <+: q0 :: q' ∧ ¬ q0 :: q' <+: [a, z] := by
      by_cases hqa : q0 = a
      · have hpa : p0 ≠ a := fun h => hbad ⟨h, hqa⟩
        have hpo : ¬ p0 :: p' <+: o0 :: o1 :: o'' := by
          rw [ho]
          exact (higmanVCTauBridge_inc_cons p' (o1 :: o'') hpa).1
        obtain ⟨hne, hpre⟩ := higmanVCTauBridge_aword_q hd hpq hqp hsm hso hlt
          (higmanVCTauBridge_inc_cons p' _ hpa).1 hpo
        exact higmanVCTauBridge_inc_moved (higmanVCTauBridge_two_le hne) hpre hFm.1 hFo.1
      · exact higmanVCTauBridge_inc_cons [z] q' (fun h => hqa h.symm)
    exact ⟨[a, z], by simp,
      higmanVCTauBridge_inc_cons [z] [] (higmanVCTauConj_other_ne hd a).symm,
      higmanVCTauBridge_inc_pair [c] hzb, hFm, hFo, hp_ok, hq_ok⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_three_eq

/-- **Fresh words, `o₀ ≠ a`.** -/
theorem higmanVCTauBridge_three_ne {d : ℕ} (hd3 : 3 ≤ d) {a b c k o0 p0 q0 : Fin d}
    {t o' p' q' m' o2 : List (Fin d)} (ho : o0 ≠ a)
    (hpq : ¬ p0 :: p' <+: q0 :: q') (hqp : ¬ q0 :: q' <+: p0 :: p')
    (hsm : MapsCone (coneSwap _ _ hpq hqp) (a :: b :: c :: k :: t) m')
    (hso : MapsCone (coneSwap _ _ hpq hqp) (o0 :: o') o2)
    (hlt : m'.length + o2.length < (a :: b :: c :: k :: t).length + (o0 :: o').length) :
    ∃ F, higmanVCTauBridge_FreshMO d (p0 :: p') (q0 :: q') (a :: b :: c :: k :: t)
      (o0 :: o') F := by
  have hd : 1 < d := by omega
  unfold higmanVCTauBridge_FreshMO
  have hQ : (a :: b :: c :: k :: t).take 3 = a :: [b, c] := rfl
  have hdesc : higmanVCTau_descP (a :: b :: c :: k :: t) (o0 :: o') =
      if (o0 :: o').head? = some a then [higmanVCTau_other a]
      else [a, higmanVCTau_other b] := rfl
  have hh : ¬ (o0 :: o').head? = some a := by
    rw [List.head?_cons, Option.some.injEq]
    exact ho
  rw [hQ, hdesc, if_neg hh]
  by_cases hbad : (p0 = a ∨ p0 = o0) ∧ (q0 = a ∨ q0 = o0)
  · obtain ⟨e, h1, h2⟩ := higmanVCTauBridge_avoid2 hd3 a o0
    have hep : e ≠ p0 := by rcases hbad.1 with h | h <;> rw [h] <;> assumption
    have heq : e ≠ q0 := by rcases hbad.2 with h | h <;> rw [h] <;> assumption
    exact ⟨[e], by simp, higmanVCTauBridge_inc_single _ h1,
      higmanVCTauBridge_inc_single [b, c] h1, higmanVCTauBridge_inc_single _ h1,
      higmanVCTauBridge_inc_single o' h2, higmanVCTauBridge_inc_single p' hep,
      higmanVCTauBridge_inc_single q' heq⟩
  · obtain ⟨z, hzb, hzob⟩ := higmanVCTauBridge_avoid2 hd3 b (higmanVCTau_other b)
    have hFm : ¬ [a, z] <+: a :: b :: c :: k :: t ∧ ¬ a :: b :: c :: k :: t <+: [a, z] :=
      higmanVCTauBridge_inc_pair _ hzb
    have hFo : ¬ [a, z] <+: o0 :: o' ∧ ¬ o0 :: o' <+: [a, z] :=
      higmanVCTauBridge_inc_cons [z] o' (fun h => ho h.symm)
    have hp_ok : ¬ [a, z] <+: p0 :: p' ∧ ¬ p0 :: p' <+: [a, z] := by
      by_cases hpa : p0 = a
      · have hq : ¬ (q0 = a ∨ q0 = o0) := fun h => hbad ⟨Or.inl hpa, h⟩
        obtain ⟨hne, hpre⟩ := higmanVCTauBridge_aword_p hd hpq hqp hsm hso hlt
          (higmanVCTauBridge_inc_cons q' _ (fun h => hq (Or.inl h))).1
          (higmanVCTauBridge_inc_cons q' o' (fun h => hq (Or.inr h))).1
        exact higmanVCTauBridge_inc_moved (higmanVCTauBridge_two_le hne) hpre hFm.1 hFo.1
      · exact higmanVCTauBridge_inc_cons [z] p' (fun h => hpa h.symm)
    have hq_ok : ¬ [a, z] <+: q0 :: q' ∧ ¬ q0 :: q' <+: [a, z] := by
      by_cases hqa : q0 = a
      · have hp : ¬ (p0 = a ∨ p0 = o0) := fun h => hbad ⟨h, Or.inl hqa⟩
        obtain ⟨hne, hpre⟩ := higmanVCTauBridge_aword_q hd hpq hqp hsm hso hlt
          (higmanVCTauBridge_inc_cons p' _ (fun h => hp (Or.inl h))).1
          (higmanVCTauBridge_inc_cons p' o' (fun h => hp (Or.inr h))).1
        exact higmanVCTauBridge_inc_moved (higmanVCTauBridge_two_le hne) hpre hFm.1 hFo.1
      · exact higmanVCTauBridge_inc_cons [z] q' (fun h => hqa h.symm)
    exact ⟨[a, z], by simp, higmanVCTauBridge_inc_pair [] hzob,
      higmanVCTauBridge_inc_pair [c] hzb, hFm, hFo, hp_ok, hq_ok⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_three_ne

/-- **Fresh words (main/other form) on at least three letters.** -/
theorem higmanVCTauBridge_fresh_mo3 {d : ℕ} (hd3 : 3 ≤ d) {m o p q m' o' : List (Fin d)}
    (hm : 4 ≤ m.length) (hom : ¬ o <+: m) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hsm : MapsCone (coneSwap p q hpq hqp) m m') (hso : MapsCone (coneSwap p q hpq hqp) o o')
    (hlt : m'.length + o'.length < m.length + o.length) :
    ∃ F, higmanVCTauBridge_FreshMO d p q m o F := by
  rcases m with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨k, t⟩⟩⟩⟩
  · simp at hm
  · simp at hm
  · simp at hm
  · simp at hm
  rcases o with _ | ⟨o0, o''⟩
  · exact (hom List.nil_prefix).elim
  rcases p with _ | ⟨p0, p'⟩
  · exact (hpq List.nil_prefix).elim
  rcases q with _ | ⟨q0, q'⟩
  · exact (hqp List.nil_prefix).elim
  by_cases ho : o0 = a
  · rcases o'' with _ | ⟨o1, o3⟩
    · refine (hom ?_).elim
      rw [ho]
      exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
    · exact higmanVCTauBridge_three_eq hd3 ho hpq hqp hsm hso hlt
  · exact higmanVCTauBridge_three_ne hd3 ho hpq hqp hsm hso hlt

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_fresh_mo3

/-- **Fresh words exist on at least three letters.**  Every lower-level instance on `d ≥ 3`
letters has a fresh bridge word. -/
theorem higmanVCTauBridge_fresh_exists3 {d : ℕ} (hd3 : 3 ≤ d) {p q x y x' y' : List (Fin d)}
    (hlong : ¬ (x.length ≤ 3 ∧ y.length ≤ 3)) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hlt : x'.length + y'.length < x.length + y.length) :
    ∃ F, higmanVCTauBridge_Fresh d p q x y F := by
  unfold higmanVCTauBridge_Fresh
  by_cases hl : y.length ≤ x.length
  · have e1 : higmanVCTau_pP (x, y) = higmanVCTau_descP x y := if_pos hl
    have e2 : higmanVCTau_pQ (x, y) = x.take 3 := if_pos hl
    have hx4 : 4 ≤ x.length := by
      by_contra h
      exact hlong ⟨by omega, by omega⟩
    rw [e1, e2]
    obtain ⟨F, hF⟩ := higmanVCTauBridge_fresh_mo3 hd3 hx4 hyx hpq hqp hmx hmy hlt
    unfold higmanVCTauBridge_FreshMO at hF
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF
    exact ⟨F, h1, h2, h3, h4, h5, h6, h7⟩
  · have e1 : higmanVCTau_pP (x, y) = higmanVCTau_descP y x := if_neg hl
    have e2 : higmanVCTau_pQ (x, y) = y.take 3 := if_neg hl
    have hy4 : 4 ≤ y.length := by
      by_contra h
      exact hlong ⟨by omega, by omega⟩
    rw [e1, e2]
    obtain ⟨F, hF⟩ := higmanVCTauBridge_fresh_mo3 hd3 hy4 hxy hpq hqp hmy hmx (by omega)
    unfold higmanVCTauBridge_FreshMO at hF
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF
    exact ⟨F, h1, h2, h3, h5, h4, h6, h7⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_fresh_exists3

end GroupApproximation.BooneHigman.Metabelian.Envelope
