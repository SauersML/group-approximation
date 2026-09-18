import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauHopF2Words
import GroupApproximation.Meta.AxiomGuard

/-!
# Hop family F2: the descent candidates (lane bh-met-92n)

For `x = a b c z` the length-`2` descent candidates are `[a, b']` (`b' ≠ b`) and `[a', e]`
(`a' ≠ a`).  A word through `[a, b]` blocks none of them (`higmanVCTauHop_candNb`), and over
`Fin 2` two words of length `≥ 2` never block all of them (`higmanVCTauHop_pick`); a free
candidate gives a flexible square B (`higmanVCTauHop_flexBc`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The descent candidates of `u = [a, b, c]` are incomparable with `u` and of length `2`. -/
theorem higmanVCTauHop_candInc {d : ℕ} {v : List (Fin d)} {a b c a' b' : Fin d}
    (ha : a' ≠ a) (hb : b' ≠ b) (hv : v = [a, b'] ∨ ∃ e, v = [a', e]) :
    higmanVCTauUnif_Inc v [a, b, c] ∧ v.length = 2 := by
  rcases hv with rfl | ⟨e, rfl⟩
  · exact ⟨higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons hb [] [c]), rfl⟩
  · exact ⟨higmanVCTauUnif_inc_cons ha [e] [b, c], rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_candInc

/-- A word through `[a, b]` blocks no descent candidate. -/
theorem higmanVCTauHop_candNb {d : ℕ} {v W : List (Fin d)} {a b a' b' : Fin d}
    (ha : a' ≠ a) (hb : b' ≠ b) (hv : v = [a, b'] ∨ ∃ e, v = [a', e]) (hW : [a, b] <+: W) :
    ¬ v <+: W := by
  obtain ⟨t, rfl⟩ := hW
  rcases hv with rfl | ⟨e, rfl⟩
  · intro h
    have h' : a :: [b'] <+: a :: b :: t := h
    exact hb (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h').2).1
  · intro h
    have h' : a' :: [e] <+: a :: b :: t := h
    exact ha (List.cons_prefix_cons.mp h').1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_candNb

/-- **A free descent candidate.**  Over `Fin 2`, for two words of length `≥ 2` one of the
candidates `[a, b']`, `[a', e]` is a prefix of neither. -/
theorem higmanVCTauHop_pick {a a' b' : Fin 2} (ha : a' ≠ a) {W1 W2 : List (Fin 2)}
    (h1 : 2 ≤ W1.length) (h2 : 2 ≤ W2.length) :
    ∃ v : List (Fin 2), (v = [a, b'] ∨ ∃ e, v = [a', e]) ∧ ¬ v <+: W1 ∧ ¬ v <+: W2 := by
  by_cases k1 : [a, b'] <+: W1
  · obtain ⟨t, rfl⟩ := k1
    rcases W2 with _ | ⟨s2, _ | ⟨t2, r2⟩⟩
    · simp at h2
    · simp at h2
    · obtain ⟨e, he⟩ := higmanVCTauBin_flip t2
      refine ⟨[a', e], Or.inr ⟨e, rfl⟩, fun h => ha ?_, fun h => he ?_⟩
      · have h' : a' :: [e] <+: a :: b' :: t := h
        exact (List.cons_prefix_cons.mp h').1
      · have h' : a' :: [e] <+: s2 :: t2 :: r2 := h
        exact (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h').2).1
  · by_cases k2 : [a, b'] <+: W2
    · obtain ⟨t, rfl⟩ := k2
      rcases W1 with _ | ⟨s1, _ | ⟨t1, r1⟩⟩
      · simp at h1
      · simp at h1
      · obtain ⟨e, he⟩ := higmanVCTauBin_flip t1
        refine ⟨[a', e], Or.inr ⟨e, rfl⟩, fun h => he ?_, fun h => ha ?_⟩
        · have h' : a' :: [e] <+: s1 :: t1 :: r1 := h
          exact (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h').2).1
        · have h' : a' :: [e] <+: a :: b' :: t := h
          exact (List.cons_prefix_cons.mp h').1
    · exact ⟨[a, b'], Or.inl rfl, k1, k2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_pick

/-- A word off the cone of `a b c z` and not through `[a, b]` is incomparable with the
sibling `[a, b, c']`. -/
theorem higmanVCTauHop_incW {d : ℕ} {a b c c' : Fin d} {z W : List (Fin d)}
    (hab : ¬ [a, b] <+: W) (hW : ¬ W <+: a :: b :: c :: z) :
    higmanVCTauUnif_Inc W [a, b, c'] := by
  refine ⟨fun h => ?_, fun h => hab ((⟨[c'], rfl⟩ : [a, b] <+: [a, b, c']).trans h)⟩
  rcases W with _ | ⟨s, _ | ⟨t, r⟩⟩
  · exact hW List.nil_prefix
  · have h' : s :: [] <+: a :: [b, c'] := h
    have e := (List.cons_prefix_cons.mp h').1
    subst e
    exact hW (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
  · have h' : s :: t :: r <+: a :: b :: [c'] := h
    obtain ⟨e1, h2⟩ := List.cons_prefix_cons.mp h'
    obtain ⟨e2, -⟩ := List.cons_prefix_cons.mp h2
    subst e1
    subst e2
    exact hab (List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_incW

/-- **Flexible square B by a free candidate.**  If the candidate `v` of `x = a b c z` is a
prefix of none of `P'`, `Q'`, `y`, then `(P', Q'; (x, y) → (x, y))` is flexible B. -/
theorem higmanVCTauHop_flexBc {d : ℕ} {P' Q' y z v : List (Fin d)} {a b c a' b' : Fin d}
    (ha : a' ≠ a) (hb : b' ≠ b) (hv : v = [a, b'] ∨ ∃ e, v = [a', e])
    (hP2 : 2 ≤ P'.length) (hP3 : P'.length ≤ 3) (hQ2 : 2 ≤ Q'.length) (hQ3 : Q'.length ≤ 3)
    (hy2 : 2 ≤ y.length) (hPu : higmanVCTauUnif_Inc P' [a, b, c])
    (hQu : higmanVCTauUnif_Inc Q' [a, b, c]) (h1 : ¬ v <+: P') (h2 : ¬ v <+: Q')
    (h3 : ¬ v <+: y) (hyx : ¬ y <+: a :: b :: c :: z) :
    higmanVCTauComm_FlexB d P' Q' (a :: b :: c :: z) y (a :: b :: c :: z) y := by
  obtain ⟨hvu, hl⟩ := higmanVCTauHop_candInc (c := c) ha hb hv
  have e5 : ([a, b, c] : List (Fin d)).length = 3 := rfl
  exact higmanVCTauHop_flexBv (x := a :: b :: c :: z) (u := [a, b, c]) (z := z) hvu.1 hvu.2
    (by omega) (le_of_eq e5) rfl hP3 hQ3 (higmanVCTauHop_incV hl hP2 h1) hPu
    (higmanVCTauHop_incV hl hQ2 h2) hQu (higmanVCTauHop_incV hl hy2 h3) hyx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_flexBc

end GroupApproximation.BooneHigman.Metabelian.Envelope
