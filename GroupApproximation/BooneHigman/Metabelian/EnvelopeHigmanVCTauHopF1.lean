import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauHopF1Words
import GroupApproximation.Meta.AxiomGuard

/-!
# Hop family F1 is contradictory (lane bh-met-92n)

`higmanVCTauHop_f1`: an F1 instance of `HigmanVCTauBinHopStatement` (`|p| + |q| = 3`, both
source words in the cones), not all short, always has a level-`n` `HopA` either forward
`(x, y) → (x', y')` or backward `(x', y') → (x, y)`; so the two hypotheses `¬ HopA` of the
residual are contradictory there.  The positions `PP` / `QQ` break the equal level, `PQ` /
`QP` with `y = b c t₀ t'` use `higmanVCTauHop_hopA` forward, and `y = b c` uses it on the
reversed and mirrored instance.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The F1 `HopA` witness.**  For any cone swap `s` with `[a] ↦ [b, c] ↦ [a]` fixing all
words incomparable with both, the instance `(a r, b c t₀ t') → (b c r, a t₀ t')` has a
`HopA` at its level, unless `r = t' = []`. -/
theorem higmanVCTauHop_hopA {d n : ℕ} {p q : List (Fin d)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} {a b c c' t0 : Fin d} {r t' : List (Fin d)}
    (hs1 : MapsCone (coneSwap p q hpq hqp) [a] [b, c])
    (hs2 : MapsCone (coneSwap p q hpq hqp) [b, c] [a])
    (hfix : ∀ u : List (Fin d), higmanVCTauUnif_Inc u [a] → higmanVCTauUnif_Inc u [b, c] →
      MapsCone (coneSwap p q hpq hqp) u u)
    (hab : a ≠ b) (hc : c' ≠ c) (hn : r.length + t'.length + 4 = n)
    (hne : r ≠ [] ∨ t' ≠ []) :
    higmanVCTauLevel_HopA d n p q (a :: r) (b :: c :: t0 :: t') (b :: c :: r) (a :: t0 :: t')
      hpq hqp := by
  have hi := higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons hc [] [t0])
  have hj := higmanVCTauUnif_inc_cons (Ne.symm hab) [c'] [t0]
  have e1 : (a :: r).length = r.length + 1 := rfl
  have e2 : (b :: c' :: t').length = t'.length + 1 + 1 := rfl
  have e3 : (b :: c :: t0 :: t').length = t'.length + 1 + 1 + 1 := rfl
  have e4 : (b :: c :: r).length = r.length + 1 + 1 := rfl
  have e5 : (a :: t0 :: t').length = t'.length + 1 + 1 := rfl
  exact ⟨[b, c'], [b, c, t0], a :: r, b :: c' :: t', [b, c'], [a, t0], b :: c :: r,
    b :: c' :: t', hi.1, hi.2, by simp, by simp,
    higmanVCTauUnif_fix hi.1 hi.2 (higmanVCTauUnif_inc_cons hab r [c'])
      (higmanVCTauUnif_inc_cons hab r [c, t0]),
    (mapsCone_coneSwap_left hi.1 hi.2).append t', by omega,
    hfix _ (higmanVCTauUnif_inc_cons (Ne.symm hab) [c'] [])
      (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons hc [] [])),
    hs2.append [t0], by simp, by simp, hs1.append r,
    hfix _ (higmanVCTauUnif_inc_cons (Ne.symm hab) (c' :: t') [])
      (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons hc t' [])),
    ⟨by omega, by omega,
      Or.inr (Or.inr (Or.inl ⟨hj.1, hj.2, higmanVCTauHop_flex hab hc hj.1 hj.2 hne⟩))⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_hopA

/-- The `PQ` core: forward or backward `HopA` for `(a r, b c t) → (b c r, a t)`. -/
theorem higmanVCTauHop_core {d n : ℕ} {p q : List (Fin d)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} {a b c c' : Fin d} (r t : List (Fin d))
    (hs1 : MapsCone (coneSwap p q hpq hqp) [a] [b, c])
    (hs2 : MapsCone (coneSwap p q hpq hqp) [b, c] [a])
    (hfix : ∀ u : List (Fin d), higmanVCTauUnif_Inc u [a] → higmanVCTauUnif_Inc u [b, c] →
      MapsCone (coneSwap p q hpq hqp) u u)
    (hab : a ≠ b) (hc : c' ≠ c) (hn : r.length + t.length + 3 = n)
    (hs : ¬ ((a :: r).length ≤ 3 ∧ (b :: c :: t).length ≤ 3 ∧ (b :: c :: r).length ≤ 3 ∧
      (a :: t).length ≤ 3)) :
    higmanVCTauLevel_HopA d n p q (a :: r) (b :: c :: t) (b :: c :: r) (a :: t) hpq hqp ∨
      higmanVCTauLevel_HopA d n p q (b :: c :: r) (a :: t) (a :: r) (b :: c :: t) hpq hqp := by
  rcases t with _ | ⟨t0, t'⟩
  · rcases r with _ | ⟨r0, r'⟩
    · exact (hs ⟨by simp, by simp, by simp, by simp⟩).elim
    · have e0 : ([] : List (Fin d)).length = 0 := rfl
      have e1 : (r0 :: r').length = r'.length + 1 := rfl
      have hne : r' ≠ [] := by
        rintro rfl
        exact hs ⟨by simp, by simp, by simp, by simp⟩
      exact Or.inr (higmanVCTauUnif_hopA_swap (higmanVCTauHop_hopA (r := []) (t' := r')
        hs1 hs2 hfix hab hc (by omega) (Or.inr hne)))
  · have e1 : (t0 :: t').length = t'.length + 1 := rfl
    by_cases hne : r ≠ [] ∨ t' ≠ []
    · exact Or.inl (higmanVCTauHop_hopA hs1 hs2 hfix hab hc (by omega) hne)
    · have hr : r = [] := by
        by_contra h
        exact hne (Or.inl h)
      have ht : t' = [] := by
        by_contra h
        exact hne (Or.inr h)
      subst hr ht
      exact (hs ⟨by simp, by simp, by simp, by simp⟩).elim

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_core

/-- Length of `[a] ++ r`. -/
theorem higmanVCTauHop_lenA {X : Type*} (a : X) (r : List X) :
    ([a] ++ r).length = r.length + 1 := by
  have e : ([a] ++ r).length = [a].length + r.length := List.length_append
  have e2 : ([a] : List X).length = 1 := rfl
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_lenA

/-- Length of `[b, c] ++ r`. -/
theorem higmanVCTauHop_lenB {X : Type*} (b c : X) (r : List X) :
    ([b, c] ++ r).length = r.length + 2 := by
  have e : ([b, c] ++ r).length = [b, c].length + r.length := List.length_append
  have e2 : ([b, c] : List X).length = 2 := rfl
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_lenB

/-- A source word in one of the two cones is carried by prefix replacement. -/
theorem higmanVCTauHop_tri {p q x x' : List (Fin 2)} {hpq : ¬ p <+: q} {hqp : ¬ q <+: p}
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hx : p <+: x ∨ q <+: x) :
    (∃ r, x = p ++ r ∧ x' = q ++ r) ∨ (∃ r, x = q ++ r ∧ x' = p ++ r) := by
  rcases higmanVCTauClassify_tri (by omega) hmx with h | h | ⟨hxp, hxq, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (hx.elim hxp.2 hxq.2).elim

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_tri

/-- F1 with the cone facts of `s` abstracted (both orders of `p`, `q` at once). -/
theorem higmanVCTauHop_f1s {n : ℕ} {p q x y x' y' : List (Fin 2)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} {a b c : Fin 2}
    (hs1 : MapsCone (coneSwap p q hpq hqp) [a] [b, c])
    (hs2 : MapsCone (coneSwap p q hpq hqp) [b, c] [a])
    (hfix : ∀ u : List (Fin 2), higmanVCTauUnif_Inc u [a] → higmanVCTauUnif_Inc u [b, c] →
      MapsCone (coneSwap p q hpq hqp) u u)
    (hab : a ≠ b)
    (hx : (∃ r, x = [a] ++ r ∧ x' = [b, c] ++ r) ∨ (∃ r, x = [b, c] ++ r ∧ x' = [a] ++ r))
    (hy : (∃ t, y = [a] ++ t ∧ y' = [b, c] ++ t) ∨ (∃ t, y = [b, c] ++ t ∧ y' = [a] ++ t))
    (h1 : x.length + y.length = n) (h2 : x'.length + y'.length = n)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hA : ¬ higmanVCTauLevel_HopA 2 n p q x y x' y' hpq hqp)
    (hA' : ¬ higmanVCTauLevel_HopA 2 n p q x' y' x y hpq hqp) : False := by
  obtain ⟨c', hc⟩ := higmanVCTauBin_flip c
  rcases hx with ⟨r, rfl, rfl⟩ | ⟨r, rfl, rfl⟩ <;>
    rcases hy with ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ <;>
    have k1 := higmanVCTauHop_lenA a r <;> have k2 := higmanVCTauHop_lenA a t <;>
    have k3 := higmanVCTauHop_lenB b c r <;> have k4 := higmanVCTauHop_lenB b c t
  · omega
  · rcases higmanVCTauHop_core (n := n) r t hs1 hs2 hfix hab hc (by omega) hs with h | h
    · exact hA h
    · exact hA' h
  · rcases higmanVCTauHop_core (n := n) t r hs1 hs2 hfix hab hc (by omega)
      (fun ⟨j1, j2, j3, j4⟩ => hs ⟨j2, j1, j4, j3⟩) with h | h
    · exact hA (higmanVCTauUnif_hopA_swap h)
    · exact hA' (higmanVCTauUnif_hopA_swap h)
  · omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_f1s

/-- **Family F1 is contradictory.**  An F1 instance (`|p| + |q| = 3`, both source words in
the cones), not all short, has a level-`n` `HopA` forward or backward. -/
theorem higmanVCTauHop_f1 {n : ℕ} {p q x y x' y' : List (Fin 2)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} (hF : p.length + q.length = 3) (hx : p <+: x ∨ q <+: x)
    (hy : p <+: y ∨ q <+: y)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (h1 : x.length + y.length = n) (h2 : x'.length + y'.length = n)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hA : ¬ higmanVCTauLevel_HopA 2 n p q x y x' y' hpq hqp)
    (hA' : ¬ higmanVCTauLevel_HopA 2 n p q x' y' x y hpq hqp) : False := by
  have lp := higmanVCTauClassify_len_pos hpq
  have lq := higmanVCTauClassify_len_pos hqp
  have tx := higmanVCTauHop_tri hmx hx
  have ty := higmanVCTauHop_tri hmy hy
  rcases (by omega : (p.length = 1 ∧ q.length = 2) ∨ (p.length = 2 ∧ q.length = 1)) with
    ⟨l1, l2⟩ | ⟨l1, l2⟩
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp l1
    obtain ⟨b, c, rfl⟩ := List.length_eq_two.mp l2
    have hab : a ≠ b := by
      rintro rfl
      exact hpq ⟨[c], rfl⟩
    exact higmanVCTauHop_f1s (mapsCone_coneSwap_left hpq hqp) (mapsCone_coneSwap_right hpq hqp)
      (fun _ k1 k2 => higmanVCTauUnif_fix hpq hqp k1 k2) hab tx ty h1 h2 hs hA hA'
  · obtain ⟨b, c, rfl⟩ := List.length_eq_two.mp l1
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp l2
    have hab : a ≠ b := by
      rintro rfl
      exact hqp ⟨[c], rfl⟩
    exact higmanVCTauHop_f1s (mapsCone_coneSwap_right hpq hqp) (mapsCone_coneSwap_left hpq hqp)
      (fun _ k1 k2 => higmanVCTauUnif_fix hpq hqp k2 k1) hab tx.symm ty.symm h1 h2 hs hA hA'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_f1

end GroupApproximation.BooneHigman.Metabelian.Envelope
