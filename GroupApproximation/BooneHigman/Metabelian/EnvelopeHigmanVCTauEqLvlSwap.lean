import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauConjWords
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauCommOptions
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeThreeWords
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Abstract cone swaps and the flexible-A shape (lane bh-met-77z)

* `higmanVCTauEqLvl_Sw σ a b`: `σ` is an involution that swaps the cones of the incomparable
  words `a` and `b` and fixes every word incomparable with both.
* `higmanVCTauEqLvl_cases`: a prefix substitution of such a `σ` has one of three forms.
* `higmanVCTauEqLvl_FA σ x y`: the body of `higmanVCTauComm_FlexA`, with the cone swap `(p q)`
  replaced by `σ`.
* Symmetry lemmas for `FA` and `higmanVCTauComm_FlexB`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `σ` swaps the cones of the incomparable words `a`, `b` and fixes the incomparable words. -/
def higmanVCTauEqLvl_Sw {d : ℕ} (σ : Equiv.Perm (Cantor (Fin d)))
    (a b : List (Fin d)) : Prop :=
  ¬ a <+: b ∧ ¬ b <+: a ∧ σ * σ = 1 ∧ MapsCone σ a b ∧ MapsCone σ b a ∧
    ∀ w : List (Fin d), ¬ w <+: a → ¬ a <+: w → ¬ w <+: b → ¬ b <+: w → MapsCone σ w w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_Sw

/-- The roles of `a` and `b` are symmetric. -/
theorem higmanVCTauEqLvl_sw_symm {d : ℕ} {σ : Equiv.Perm (Cantor (Fin d))}
    {a b : List (Fin d)} (h : higmanVCTauEqLvl_Sw σ a b) : higmanVCTauEqLvl_Sw σ b a := by
  obtain ⟨hab, hba, hσ, ha, hb, hfix⟩ := h
  exact ⟨hba, hab, hσ, hb, ha, fun w h1 h2 h3 h4 => hfix w h3 h4 h1 h2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_sw_symm

/-- A cone swap is an abstract cone swap. -/
theorem higmanVCTauEqLvl_sw_coneSwap {d : ℕ} {p q : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : higmanVCTauEqLvl_Sw (coneSwap p q hpq hqp) p q :=
  ⟨hpq, hqp, coneSwap_mul_self hpq hqp, mapsCone_coneSwap_left hpq hqp,
    mapsCone_coneSwap_right hpq hqp,
    fun _ h1 h2 h3 h4 => vgen_mapsCone_coneSwap_fix hpq hqp h1 h2 h3 h4⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_sw_coneSwap

/-- **The three forms** of a prefix substitution `w ↦ w'` of an abstract cone swap. -/
theorem higmanVCTauEqLvl_cases {d : ℕ} (hd : 1 < d) {σ : Equiv.Perm (Cantor (Fin d))}
    {a b w w' : List (Fin d)} (hs : higmanVCTauEqLvl_Sw σ a b) (h : MapsCone σ w w') :
    (∃ u, w = a ++ u ∧ w' = b ++ u) ∨ (∃ u, w = b ++ u ∧ w' = a ++ u) ∨
      (¬ w <+: a ∧ ¬ a <+: w ∧ ¬ w <+: b ∧ ¬ b <+: w ∧ w' = w) := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨hab, hba, hσ, ha, hb, hfix⟩ := hs
  have hne : a ≠ b := fun e => by
    subst e
    exact hab (List.prefix_refl _)
  by_cases h1 : a <+: w
  · obtain ⟨u, rfl⟩ := h1
    exact Or.inl ⟨u, rfl, MapsCone.unique h (ha.append u)⟩
  by_cases h2 : b <+: w
  · obtain ⟨u, rfl⟩ := h2
    exact Or.inr (Or.inl ⟨u, rfl, MapsCone.unique h (hb.append u)⟩)
  have h3 : ¬ w <+: a := fun h3 => by
    have e := higmanVCTauConj_eq_of_prefix_core hσ ha hb hfix hne h h3
    subst e
    exact h1 (List.prefix_refl _)
  have h4 : ¬ w <+: b := fun h4 => by
    have e := higmanVCTauConj_eq_of_prefix_core hσ hb ha
      (fun v g1 g2 g3 g4 => hfix v g3 g4 g1 g2) (Ne.symm hne) h h4
    subst e
    exact h2 (List.prefix_refl _)
  exact Or.inr (Or.inr ⟨h3, h1, h4, h2, MapsCone.unique h (hfix w h3 h1 h4 h2)⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_cases

/-- **The flexible-A shape** with the second cone swap replaced by `σ`. -/
def higmanVCTauEqLvl_FA {d : ℕ} (σ : Equiv.Perm (Cantor (Fin d)))
    (x y : List (Fin d)) : Prop :=
  ∃ (P Q X Y P' Q' X' Y' : List (Fin d)) (hPQ : ¬ P <+: Q) (hQP : ¬ Q <+: P),
    P.length ≤ 3 ∧ Q.length ≤ 3 ∧
    MapsCone (coneSwap P Q hPQ hQP) X x ∧ MapsCone (coneSwap P Q hPQ hQP) Y y ∧
    X.length + Y.length < x.length + y.length ∧
    MapsCone σ P P' ∧ MapsCone σ Q Q' ∧
    P'.length ≤ 3 ∧ Q'.length ≤ 3 ∧
    MapsCone σ X X' ∧ MapsCone σ Y Y' ∧
    X'.length + Y'.length < x.length + y.length

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_FA

/-- At `σ = (p q)` the shape is flexible A. -/
theorem higmanVCTauEqLvl_flexA_of_FA {d : ℕ} {p q x y : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (h : higmanVCTauEqLvl_FA (coneSwap p q hpq hqp) x y) :
    higmanVCTauComm_FlexA d p q x y hpq hqp :=
  h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_flexA_of_FA

/-- The shape is symmetric in the pair. -/
theorem higmanVCTauEqLvl_FA_swap {d : ℕ} {σ : Equiv.Perm (Cantor (Fin d))}
    {x y : List (Fin d)} (h : higmanVCTauEqLvl_FA σ x y) : higmanVCTauEqLvl_FA σ y x := by
  obtain ⟨P, Q, X, Y, P', Q', X', Y', hPQ, hQP, hP, hQ, hX, hY, hC, hP', hQ', hP3, hQ3,
    hX', hY', hC'⟩ := h
  exact ⟨P, Q, Y, X, P', Q', Y', X', hPQ, hQP, hP, hQ, hY, hX, by omega, hP', hQ', hP3, hQ3,
    hY', hX', by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_FA_swap

/-- Flexible B is symmetric in the pair. -/
theorem higmanVCTauEqLvl_flexB_swap {d : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauComm_FlexB d p q x y x' y') : higmanVCTauComm_FlexB d p q y x y' x' := by
  obtain ⟨P, Q, X, Y, p1, q1, D1, D2, hPQ, hQP, hP, hQ, hX, hY, hC, hp1, hq1, hp3, hq3,
    hD1, hD2, hC'⟩ := h
  exact ⟨P, Q, Y, X, p1, q1, D2, D1, hPQ, hQP, hP, hQ, hY, hX, by omega, hp1, hq1, hp3, hq3,
    hD2, hD1, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_flexB_swap

/-- Flexible B is symmetric in the cone swap. -/
theorem higmanVCTauEqLvl_flexB_pq {d : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauComm_FlexB d p q x y x' y') : higmanVCTauComm_FlexB d q p x y x' y' := by
  obtain ⟨P, Q, X, Y, p1, q1, D1, D2, hPQ, hQP, hP, hQ, hX, hY, hC, hp1, hq1, hp3, hq3,
    hD1, hD2, hC'⟩ := h
  exact ⟨P, Q, X, Y, q1, p1, D1, D2, hPQ, hQP, hP, hQ, hX, hY, hC, hq1, hp1, hq3, hp3,
    hD1, hD2, hC'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_flexB_pq

end GroupApproximation.BooneHigman.Metabelian.Envelope
