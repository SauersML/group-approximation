import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3VacFlexA
import GroupApproximation.Meta.AxiomGuard

/-!
# Word lemmas for the unequal-length case (lane bh-met-92x)

* `higmanVCTauFix3Vac_cls`: a word `z` with `(p q) z = z'` is `p u ↦ q u`, `q u ↦ p u`, or
  fixed with neither `p` nor `q` a prefix;
* `higmanVCTauFix3Vac_incOf`: in the fixed case `z` is incomparable with `p` and with `q`;
* `higmanVCTauFix3Vac_crossSwap`: the cross family is symmetric in `x ↔ y`;
* `higmanVCTauFix3Vac_pstar`: a length-2 word incomparable with a length-3 word and a
  nonempty word;
* `higmanVCTauFix3Vac_fbSwapPQ`, `higmanVCTauFix3Vac_fbSwapXY`: flexible B is symmetric in
  `p ↔ q` and in `(x, x') ↔ (y, y')`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Classification of a cone image.** -/
theorem higmanVCTauFix3Vac_cls {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z') :
    (∃ u, z = p ++ u ∧ z' = q ++ u) ∨ (∃ u, z = q ++ u ∧ z' = p ++ u) ∨
      ((¬ p <+: z ∧ ¬ q <+: z) ∧ z' = z) := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  by_cases h1 : p <+: z
  · obtain ⟨u, rfl⟩ := h1
    exact Or.inl ⟨u, rfl, h.unique ((mapsCone_coneSwap_left hpq hqp).append u)⟩
  by_cases h2 : q <+: z
  · obtain ⟨u, rfl⟩ := h2
    exact Or.inr (Or.inl ⟨u, rfl, h.unique ((mapsCone_coneSwap_right hpq hqp).append u)⟩)
  exact Or.inr (Or.inr ⟨⟨h1, h2⟩, higmanVCTauBridge_eq_of_not hd hpq hqp h h1 h2⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_cls

/-- **A fixed word is incomparable** with `p` and with `q`. -/
theorem higmanVCTauFix3Vac_incOf {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (h1 : ¬ p <+: z) (h2 : ¬ q <+: z) :
    (¬ z <+: p ∧ ¬ p <+: z) ∧ (¬ z <+: q ∧ ¬ q <+: z) := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  refine ⟨⟨fun h3 => h1 ?_, h1⟩, ⟨fun h3 => h2 ?_, h2⟩⟩
  · exact Eq.subst (motive := fun u => p <+: u)
      (higmanVCTauConj_eq_of_prefix_left hpq hqp h h3).symm (List.prefix_refl p)
  · exact Eq.subst (motive := fun u => q <+: u)
      (higmanVCTauConj_eq_of_prefix_right hpq hqp h h3).symm (List.prefix_refl q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_incOf

/-- The cross family is symmetric in `x ↔ y`. -/
theorem higmanVCTauFix3Vac_crossSwap {d : ℕ} {p q x y : List (Fin d)}
    (h : higmanVCTauDecomp_Cross p q x y) : higmanVCTauDecomp_Cross p q y x := by
  unfold higmanVCTauDecomp_Cross at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_crossSwap

/-- **A short separating word.**  For `1 < d`, `|lg| = 3` and `sh ≠ []`, some length-2 word is
incomparable with `lg` and with `sh`. -/
theorem higmanVCTauFix3Vac_pstar {d : ℕ} (hd : 1 < d) {lg sh : List (Fin d)}
    (hlg : lg.length = 3) (h0 : sh ≠ []) :
    ∃ z : List (Fin d), z.length = 2 ∧ (¬ z <+: lg ∧ ¬ lg <+: z) ∧
      (¬ z <+: sh ∧ ¬ sh <+: z) := by
  have ho := higmanVCTauSplit_other_ne hd
  rcases lg with _ | ⟨l0, _ | ⟨l1, lg'⟩⟩
  · simp at hlg
  · simp at hlg
  rcases sh with _ | ⟨s0, sh'⟩
  · exact absurd rfl h0
  by_cases hs : s0 = l0
  · exact ⟨[higmanVCTau_other l0, l0], rfl, higmanVCTauBridge_inc_cons [l0] (l1 :: lg') (ho l0),
      higmanVCTauBridge_inc_cons [l0] sh' (fun h => ho l0 (h.trans hs))⟩
  · exact ⟨[l0, higmanVCTau_other l1], rfl, higmanVCTauD2_inc2 [] lg' (ho l1),
      higmanVCTauBridge_inc_cons [higmanVCTau_other l1] sh' (Ne.symm hs)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_pstar

/-- Flexible B is symmetric in `p ↔ q`. -/
theorem higmanVCTauFix3Vac_fbSwapPQ {d : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauComm_FlexB d p q x y x' y') : higmanVCTauComm_FlexB d q p x y x' y' := by
  unfold higmanVCTauComm_FlexB at h ⊢
  obtain ⟨P, Q, X, Y, p1, q1, D1, D2, hPQ, hQP, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12⟩ := h
  exact ⟨P, Q, X, Y, q1, p1, D1, D2, hPQ, hQP, h1, h2, h3, h4, h5, h7, h6, h9, h8, h10, h11,
    h12⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_fbSwapPQ

/-- Flexible B is symmetric in `(x, x') ↔ (y, y')`. -/
theorem higmanVCTauFix3Vac_fbSwapXY {d : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauComm_FlexB d p q x y x' y') : higmanVCTauComm_FlexB d p q y x y' x' := by
  unfold higmanVCTauComm_FlexB at h ⊢
  obtain ⟨P, Q, X, Y, p1, q1, D1, D2, hPQ, hQP, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12⟩ := h
  exact ⟨P, Q, Y, X, p1, q1, D2, D1, hPQ, hQP, h1, h2, h4, h3, by omega, h6, h7, h8, h9, h11,
    h10, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_fbSwapXY

end GroupApproximation.BooneHigman.Metabelian.Envelope
