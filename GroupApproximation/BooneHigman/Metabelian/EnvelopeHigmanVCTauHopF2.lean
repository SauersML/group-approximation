import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauHopF2Hop
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauHopF1
import GroupApproximation.Meta.AxiomGuard

/-!
# The binary hop families (lane bh-met-92n)

Family F2 of `higmanVCTauBin_Hop`: `|p| = |q| = 3` and `x, y` incomparable with `p` and `q`,
so `x' = x`, `y' = y`.  Up to swapping `x`, `y`, `x = a b c z₀ z'` with `u := [a, b, c]`
(`higmanVCTauHop_f2core`):
* `y = [a']`: the one-letter hop `higmanVCTauHop_hopC1`;
* `|y| ≥ 2` and one of `p`, `q`, `y` through `[a, b]`: a flexible square B by a free
  descent candidate (`higmanVCTauHop_pick`, `higmanVCTauHop_flexBc`);
* otherwise the `w`-hop `higmanVCTauHop_hopCw` with the sibling `w := [a, b, c']` of `u`.
With family F1 (`higmanVCTauHop_f1`) this proves `HigmanVCTauBinHopStatement`, hence
`HigmanVCTauClassifyTwoStatement` and `HigmanVCTauDeepResidualStatement`.

Truth check: scratch `bh-met-92n/plan.cpp` replays exactly this case split (with the faithful
model of `FlexB`, `Easy`, `HopC` of `bh-met-92n/lib.h`) on every F2 instance with
`|x|, |y| ≤ 8`: 7870752 instances, 0 failures.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Family F2, `|x| ≥ 4`.**  A flexible square B or a `HopC` witness. -/
theorem higmanVCTauHop_f2core {n : ℕ} {p q x y : List (Fin 2)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hp3 : p.length = 3) (hq3 : q.length = 3)
    (hxp : higmanVCTauUnif_Inc x p) (hxq : higmanVCTauUnif_Inc x q)
    (hyp : higmanVCTauUnif_Inc y p) (hyq : higmanVCTauUnif_Inc y q) (hyx : ¬ y <+: x)
    (hx4 : 4 ≤ x.length) (hn : x.length + y.length = n) :
    higmanVCTauComm_FlexB 2 p q x y x y ∨ higmanVCTauLevel_HopC 2 n p q x y x y := by
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨z0, z'⟩⟩⟩⟩
  · simp at hx4
  · simp at hx4
  · simp at hx4
  · simp at hx4
  obtain ⟨a', ha⟩ := higmanVCTauBin_flip a
  obtain ⟨b', hb⟩ := higmanVCTauBin_flip b
  obtain ⟨c', hc⟩ := higmanVCTauBin_flip c
  have L1 : (a :: b :: c :: z0 :: z').length = z'.length + 1 + 1 + 1 + 1 := rfl
  have L4 : ([a, b, c] : List (Fin 2)).length = 3 := rfl
  have hpu : higmanVCTauUnif_Inc p [a, b, c] :=
    higmanVCTauHop_incU (u := [a, b, c]) (x := a :: b :: c :: z0 :: z') (z := z0 :: z') rfl
      hxp.2 (by omega)
  have hqu : higmanVCTauUnif_Inc q [a, b, c] :=
    higmanVCTauHop_incU (u := [a, b, c]) (x := a :: b :: c :: z0 :: z') (z := z0 :: z') rfl
      hxq.2 (by omega)
  rcases y with _ | ⟨s, _ | ⟨t, r⟩⟩
  · exact absurd List.nil_prefix hyx
  · -- `y = [s]`: the one-letter hop
    have hs : s ≠ a := by
      rintro rfl
      exact hyx ⟨b :: c :: z0 :: z', rfl⟩
    obtain ⟨e, he⟩ := higmanVCTauBin_flip z0
    have L2 : ([s] : List (Fin 2)).length = 1 := rfl
    exact Or.inr (higmanVCTauHop_hopC1 hs hb he hp3 hq3 (higmanVCTauUnif_incS hyp)
      (higmanVCTauUnif_incS hyq) hpu hqu (by omega))
  · -- `|y| ≥ 2`
    have L3 : (s :: t :: r).length = r.length + 1 + 1 := rfl
    have hy2 : 2 ≤ (s :: t :: r).length := by omega
    by_cases kp : [a, b] <+: p
    · obtain ⟨v, hv, h2, h3⟩ :=
        higmanVCTauHop_pick (b' := b') ha (W1 := q) (W2 := s :: t :: r) (by omega) hy2
      exact Or.inl (higmanVCTauHop_flexBc ha hb hv (by omega) (by omega) (by omega)
        (by omega) hy2 hpu hqu (higmanVCTauHop_candNb ha hb hv kp) h2 h3 hyx)
    by_cases kq : [a, b] <+: q
    · obtain ⟨v, hv, h1, h3⟩ :=
        higmanVCTauHop_pick (b' := b') ha (W1 := p) (W2 := s :: t :: r) (by omega) hy2
      exact Or.inl (higmanVCTauHop_flexBc ha hb hv (by omega) (by omega) (by omega)
        (by omega) hy2 hpu hqu h1 (higmanVCTauHop_candNb ha hb hv kq) h3 hyx)
    by_cases ky : [a, b] <+: s :: t :: r
    · obtain ⟨v, hv, h1, h2⟩ :=
        higmanVCTauHop_pick (b' := b') ha (W1 := p) (W2 := q) (by omega) (by omega)
      exact Or.inl (higmanVCTauHop_flexBc ha hb hv (by omega) (by omega) (by omega)
        (by omega) hy2 hpu hqu h1 h2 (higmanVCTauHop_candNb ha hb hv ky) hyx)
    -- the `w`-hop, `w = [a, b, c']`
    have Lw : ([a, b, c'] : List (Fin 2)).length = 3 := rfl
    have hpw : higmanVCTauUnif_Inc p [a, b, c'] := higmanVCTauHop_incW kp hxp.2
    have hqw : higmanVCTauUnif_Inc q [a, b, c'] := higmanVCTauHop_incW kq hxq.2
    have hyw : higmanVCTauUnif_Inc (s :: t :: r) [a, b, c'] := higmanVCTauHop_incW ky hyx
    have hwu : higmanVCTauUnif_Inc [a, b, c'] [a, b, c] :=
      higmanVCTauClassify_inc_cons2 a
        (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons hc [] []))
    have hwx : higmanVCTauUnif_Inc (a :: b :: c :: z0 :: z') [a, b, c'] :=
      higmanVCTauUnif_incS (higmanVCTauClassify_inc_cons2 a
        (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons hc [] (z0 :: z'))))
    have hab : [a, b] <+: [a, b, c'] := ⟨[c'], rfl⟩
    obtain ⟨v1, hv1, k1, k3⟩ :=
      higmanVCTauHop_pick (b' := b') ha (W1 := p) (W2 := s :: t :: r) (by omega) hy2
    obtain ⟨v2, hv2, k2, k3'⟩ :=
      higmanVCTauHop_pick (b' := b') ha (W1 := q) (W2 := s :: t :: r) (by omega) hy2
    have F1 := higmanVCTauHop_flexBc (P' := p) (Q' := [a, b, c']) ha hb hv1 (by omega)
      (by omega) (by omega) (by omega) hy2 hpu hwu k1 (higmanVCTauHop_candNb ha hb hv1 hab)
      k3 hyx
    have F2 := higmanVCTauHop_flexBc (P' := [a, b, c']) (Q' := q) ha hb hv2 (by omega)
      (by omega) (by omega) (by omega) hy2 hwu hqu (higmanVCTauHop_candNb ha hb hv2 hab) k2
      k3' hyx
    exact Or.inr (higmanVCTauHop_hopCw hpw.1 hpw.2 (by omega) (by omega) (by omega)
      ⟨hqp, hpq⟩ hqw hxp hwx hyp hyw hn F1 F2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_f2core

/-- **Family F2.**  Every F2 instance has a flexible square B or a `HopC` witness. -/
theorem higmanVCTauHop_f2 {n : ℕ} {p q x y x' y' : List (Fin 2)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} (hp3 : p.length = 3) (hq3 : q.length = 3)
    (hxp : higmanVCTauUnif_Inc x p) (hxq : higmanVCTauUnif_Inc x q)
    (hyp : higmanVCTauUnif_Inc y p) (hyq : higmanVCTauUnif_Inc y q)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (h1 : x.length + y.length = n)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hB : ¬ higmanVCTauComm_FlexB 2 p q x y x' y')
    (hC : ¬ higmanVCTauLevel_HopC 2 n p q x y x' y') : False := by
  have ex : x' = x := MapsCone.unique hmx (higmanVCTauUnif_fix hpq hqp hxp hxq)
  have ey : y' = y := MapsCone.unique hmy (higmanVCTauUnif_fix hpq hqp hyp hyq)
  rw [ex, ey] at hB hC hs
  by_cases hx4 : 4 ≤ x.length
  · rcases higmanVCTauHop_f2core hpq hqp hp3 hq3 hxp hxq hyp hyq hyx hx4 h1 with h | h
    · exact hB h
    · exact hC h
  · have hy4 : 4 ≤ y.length := by
      by_contra hy
      exact hs ⟨by omega, by omega, by omega, by omega⟩
    rcases higmanVCTauHop_f2core (n := n) hpq hqp hp3 hq3 hyp hyq hxp hxq hxy hy4 (by omega)
      with h | h
    · exact hB (higmanVCTauUnif_flexB_swap h)
    · exact hC (higmanVCTauUnif_hopC_swap h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_f2

/-- **The binary hop families.**  No hop-family instance escapes the flexible squares and
the hops: families F1 (`higmanVCTauHop_f1`) and F2 (`higmanVCTauHop_f2`). -/
theorem higmanVCTauHop_binHop : HigmanVCTauBinHopStatement := by
  intro n p q x y x' y' hpq hqp _ _ h1 h2 hs _ _ _ _ hFB _ _ hHA hHA' hHC hH hmx hmy hxy hyx
    _ _
  exfalso
  rcases hH with ⟨hF, hx, hy⟩ | ⟨hp3, hq3, hxp, hxq, hyp, hyq⟩
  · exact higmanVCTauHop_f1 hF hx hy hmx hmy h1 h2 hs hHA hHA'
  · exact higmanVCTauHop_f2 hp3 hq3 hxp hxq hyp hyq hmx hmy h1 hs hxy hyx hFB hHC

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_binHop

/-- **The binary classification** (`d = 2`), unconditionally. -/
theorem higmanVCTauHop_classifyTwo : HigmanVCTauClassifyTwoStatement :=
  higmanVCTauBin_classifyTwo_of_hop higmanVCTauHop_binHop

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_classifyTwo

/-- **The deep residual**, unconditionally. -/
theorem higmanVCTauHop_deep : HigmanVCTauDeepResidualStatement :=
  higmanVCTauBin_deep_of_hop higmanVCTauHop_binHop

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_deep

end GroupApproximation.BooneHigman.Metabelian.Envelope
