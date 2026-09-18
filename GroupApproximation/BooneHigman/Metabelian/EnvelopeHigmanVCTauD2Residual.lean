import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2ClassOB
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2ClassA
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2ClassAB
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-letter bridge residual, proved (lane bh-met-77v)

**Proved (symbolic, unconditional).**  `higmanVCTauD2_residual : higmanVCTauBridge_Residual`:
every `d = 2` lower-level instance without a fresh word has a descent chain.

Main word `m = a b c k t` (length `≥ 4`), other word `o`, root `(P, Q) = (descP m o, take 3 m)`.
The level-lowering short swap is `(u v)` with `|u| < |v| ≤ 3` (`higmanVCTauD2_uv_of`).  By the
first two letters of `o`:

* `o₀ ≠ a`: root or direct edge (`higmanVCTauD2_classOB`);
* `o = a o₁ …`, `o₁ ≠ b`: a bridge (`higmanVCTauD2_classA`);
* `o = a b o₂ …`: with no fresh word, a direct edge (`higmanVCTauD2_classAB`);
* `o ∈ {[], [a], [a, b]}` is a prefix of `m`, excluded.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The good position of the swap by the first two letters of the other word. -/
theorem higmanVCTauD2_good {d : ℕ} (hd : d = 2) {a b c k : Fin d}
    {t o u v m' o' : List (Fin d)} (hom : ¬ o <+: a :: b :: c :: k :: t)
    (hUV : higmanVCTauD2_UV d u v (a :: b :: c :: k :: t) o m' o')
    (hNF : higmanVCTauD2_NF d (higmanVCTau_descP (a :: b :: c :: k :: t) o) [a, b, c]
      (a :: b :: c :: k :: t) o u v) :
    higmanVCTauD2_Good d (higmanVCTau_descP (a :: b :: c :: k :: t) o) [a, b, c]
      (a :: b :: c :: k :: t) o u v m' o' := by
  have hd1 : 1 < d := by omega
  rcases o with _ | ⟨o0, o''⟩
  · exact (hom List.nil_prefix).elim
  have hdesc : higmanVCTau_descP (a :: b :: c :: k :: t) (o0 :: o'') =
      if (o0 :: o'').head? = some a then [higmanVCTau_other a]
      else [a, higmanVCTau_other b] := rfl
  rw [hdesc] at hNF ⊢
  by_cases ho : o0 = a
  · rw [ho] at hom hUV hNF ⊢
    have hh : (a :: o'').head? = some a := rfl
    rw [if_pos hh] at hNF ⊢
    rcases o'' with _ | ⟨o1, o3⟩
    · exact (hom (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)).elim
    by_cases ho1 : o1 = b
    · rw [ho1] at hom hUV hNF ⊢
      rcases o3 with _ | ⟨o2, o4⟩
      · exact (hom (List.cons_prefix_cons.mpr ⟨rfl,
          List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩⟩)).elim
      exact higmanVCTauD2_classAB (higmanVCTauConj_other_ne hd1 a)
        (higmanVCTauConj_other_ne hd1 b) (fun e he => higmanVCTauD2_bin hd he) hUV hNF
    · exact higmanVCTauD2_classA (higmanVCTauConj_other_ne hd1 a) ho1
        (fun e he => higmanVCTauD2_bin hd he)
        (fun e he => (higmanVCTauD2_bin hd he).trans (higmanVCTauD2_bin hd ho1).symm) hUV
  · have hh : ¬ (o0 :: o'').head? = some a := by
      rw [List.head?_cons, Option.some.injEq]
      exact ho
    rw [if_neg hh] at hNF ⊢
    exact higmanVCTauD2_classOB (higmanVCTauConj_other_ne hd1 b) ho
      (fun e he => (higmanVCTauD2_bin hd he).trans (higmanVCTauD2_bin hd ho).symm)
      (fun e he => higmanVCTauD2_bin hd he) hUV

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_good

/-- **The chain in main/other form** for `d = 2` without a fresh word. -/
theorem higmanVCTauD2_mo {d : ℕ} (hd : d = 2) {p q m o m' o' : List (Fin d)}
    (hm : 4 ≤ m.length) (hom : ¬ o <+: m)
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hsm : MapsCone (coneSwap p q hpq hqp) m m') (hso : MapsCone (coneSwap p q hpq hqp) o o')
    (hlt : m'.length + o'.length < m.length + o.length)
    (hnf : ∀ F, ¬ higmanVCTauBridge_FreshMO d p q m o F) :
    higmanVCTauD2_ChainMO d p q m o m' o' := by
  have hd1 : 1 < d := by omega
  have hs := higmanVCTauBridge_mkNode (higmanVCTauBridge_mkStep hpq hqp hp hq hsm hso) hlt
  rcases m with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨k, t⟩⟩⟩⟩
  · simp only [List.length_nil] at hm <;> omega
  · simp only [List.length_cons, List.length_nil] at hm <;> omega
  · simp only [List.length_cons, List.length_nil] at hm <;> omega
  · simp only [List.length_cons, List.length_nil] at hm <;> omega
  rcases higmanVCTauD2_uv_of hd1 hpq hqp hp hq hsm hso hlt with hUV | hUV
  · have hNF : higmanVCTauD2_NF d (higmanVCTau_descP (a :: b :: c :: k :: t) o) [a, b, c]
        (a :: b :: c :: k :: t) o q p := by
      unfold higmanVCTauD2_NF
      intro F h1 h2 h3 h4 h5 h6 h7
      refine hnf F ?_
      unfold higmanVCTauBridge_FreshMO
      exact ⟨h1, h2, h3, h4, h5, h7, h6⟩
    exact higmanVCTauD2_chainMO_of_good rfl rfl (Or.inr ⟨rfl, rfl⟩) hs
      (higmanVCTauD2_good hd hom hUV hNF)
  · have hNF : higmanVCTauD2_NF d (higmanVCTau_descP (a :: b :: c :: k :: t) o) [a, b, c]
        (a :: b :: c :: k :: t) o p q := by
      unfold higmanVCTauD2_NF
      intro F h1 h2 h3 h4 h5 h6 h7
      refine hnf F ?_
      unfold higmanVCTauBridge_FreshMO
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact higmanVCTauD2_chainMO_of_good rfl rfl (Or.inl ⟨rfl, rfl⟩) hs
      (higmanVCTauD2_good hd hom hUV hNF)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_mo

/-- **Proved: the two-letter bridge residual.**  Every `d = 2` lower-level instance at a
long incomparable pair without a fresh word has a descent chain. -/
theorem higmanVCTauD2_residual : higmanVCTauBridge_Residual := by
  intro d hd p q x y x' y' hpq hqp hp hq hlong hxy hyx hmx hmy hlt hnf
  unfold higmanVCTauTight_Chain
  refine ⟨hlong, ?_⟩
  by_cases hl : y.length ≤ x.length
  · have e1 : higmanVCTau_pP (x, y) = higmanVCTau_descP x y := if_pos hl
    have e2 : higmanVCTau_pQ (x, y) = x.take 3 := if_pos hl
    have hx4 : 4 ≤ x.length := by
      by_contra h
      exact hlong ⟨by omega, by omega⟩
    have hnf' : ∀ F, ¬ higmanVCTauBridge_FreshMO d p q x y F := by
      intro F hF
      unfold higmanVCTauBridge_FreshMO at hF
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF
      refine hnf F ?_
      unfold higmanVCTauBridge_Fresh
      rw [e1, e2]
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    obtain ⟨P0, Q0, X0, Y0, P1, Q1, X1, Y1, hr, h0, h1, h2, h3⟩ :=
      higmanVCTauD2_mo hd hx4 hyx hpq hqp hp hq hmx hmy hlt hnf'
    refine ⟨P0, Q0, X0, Y0, P1, Q1, X1, Y1, ?_, h0, h1, h2, h3⟩
    rw [e1, e2]
    exact hr
  · have e1 : higmanVCTau_pP (x, y) = higmanVCTau_descP y x := if_neg hl
    have e2 : higmanVCTau_pQ (x, y) = y.take 3 := if_neg hl
    have hy4 : 4 ≤ y.length := by
      by_contra h
      exact hlong ⟨by omega, by omega⟩
    have hnf' : ∀ F, ¬ higmanVCTauBridge_FreshMO d p q y x F := by
      intro F hF
      unfold higmanVCTauBridge_FreshMO at hF
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF
      refine hnf F ?_
      unfold higmanVCTauBridge_Fresh
      rw [e1, e2]
      exact ⟨h1, h2, h3, h5, h4, h6, h7⟩
    obtain ⟨P0, Q0, X0, Y0, P1, Q1, X1, Y1, hr, h0, h1, h2, h3⟩ :=
      higmanVCTauD2_mo hd hy4 hxy hpq hqp hp hq hmy hmx (by omega) hnf'
    have h2' := higmanVCTauD2_link_swap h2
    have h3' := higmanVCTauD2_link_swap h3
    rw [Nat.add_comm y.length x.length] at h2' h3'
    refine ⟨P0, Q0, Y0, X0, P1, Q1, Y1, X1, ?_, higmanVCTauBridge_node_swap h0,
      higmanVCTauBridge_node_swap h1, h2', h3'⟩
    rw [e1, e2]
    exact hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_residual

/-- **Proved (unconditional): the full chain claim** for every `d ≥ 2`. -/
theorem higmanVCTauD2_all : higmanVCTauBridge_All :=
  higmanVCTauBridge_all_of_residual higmanVCTauD2_residual

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_all

/-- **Proved (unconditional).**  The equal-level tight residual gives the tight residual. -/
theorem higmanVCTauD2_tight_of_eq (h : HigmanVCTauTightEqStatement) :
    HigmanVCTauTightStatement :=
  higmanVCTauTightEq_tight_of_eq_of_residual h higmanVCTauD2_residual

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_tight_of_eq

end GroupApproximation.BooneHigman.Metabelian.Envelope
