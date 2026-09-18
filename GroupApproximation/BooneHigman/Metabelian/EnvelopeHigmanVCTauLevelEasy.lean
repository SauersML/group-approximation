import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauCommOptions
import GroupApproximation.Meta.AxiomGuard

/-!
# Easy instances at level `n` (lane bh-met-77r)

Fix the level `n` and the level-`n` induction hypotheses `higmanVCTauShort_Below d n` and
`higmanVCTauShort_Shrink d n`.  An instance `(s; A → B)` of the conjugation family,
`s = (p, q)`, `A = (x, y)`, `B = (x', y')`, is **easy** (`higmanVCTauLevel_Easy`) when both
levels are at most `n` and either one side is strictly below `n` (then `Shrink`, possibly read
backwards, gives it) or a flexible square of lane bh-met-77m applies on one of the two sides
(`higmanVCTauComm_FlexA` / `higmanVCTauComm_FlexB`).  `higmanVCTauLevel_easy` proves every easy
instance from the two induction hypotheses.

`higmanVCTauLevel_groupC` is the group identity behind the conjugated-conjugator hop of
`EnvelopeHigmanVCTauLevelHop`: if `ℓ_r` is an involution and `ℓ_s = ℓ_r ℓ_{s1} ℓ_r⁻¹`, then
`(s; A → B)` follows from `(r; A → A1)`, `(s1; A1 → B1)` and `(r; B1 → B)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- An instance `(s; A → B)` at level `n` that the existing case lemmas prove: both levels
`≤ n`, and one side below `n` or a flexible square on one of the two sides. -/
def higmanVCTauLevel_Easy (d n : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  x.length + y.length ≤ n ∧ x'.length + y'.length ≤ n ∧
    (x.length + y.length < n ∨ x'.length + y'.length < n ∨
      (∃ (hpq : ¬ p <+: q) (hqp : ¬ q <+: p), higmanVCTauComm_FlexA d p q x y hpq hqp) ∨
      higmanVCTauComm_FlexB d p q x y x' y' ∨
      (∃ (hpq : ¬ p <+: q) (hqp : ¬ q <+: p), higmanVCTauComm_FlexA d p q x' y' hpq hqp) ∨
      higmanVCTauComm_FlexB d p q x' y' x y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_Easy

/-- **Easy instances.**  Every easy instance follows from the level-`n` hypotheses. -/
theorem higmanVCTauLevel_easy {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x')
    (hE : higmanVCTauLevel_Easy d n p q x y x' y') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  obtain ⟨h1, h2, hc⟩ := hE
  have hss := coneSwap_mul_self hpq hqp
  have hmx' : MapsCone (coneSwap p q hpq hqp) x' x := higmanVCTauConj_mapsCone_symm hmx hss
  have hmy' : MapsCone (coneSwap p q hpq hqp) y' y := higmanVCTauConj_mapsCone_symm hmy hss
  by_cases hlt : x.length + y.length < n
  · exact hS p q x y x' y' hlt h2 hpq hqp hp hq hmx hmy hxy hyx hxy' hyx'
  by_cases hlt' : x'.length + y'.length < n
  · exact higmanVCTauComm_flip_eq hp hq
      (hS p q x' y' x y hlt' h1 hpq hqp hp hq hmx' hmy' hxy' hyx' hxy hyx)
  have hA : x.length + y.length = n := by omega
  have hA' : x'.length + y'.length = n := by omega
  rcases hc with hc | hc | ⟨_, _, hF⟩ | hF | ⟨_, _, hF⟩ | hF
  · exact absurd hc hlt
  · exact absurd hc hlt'
  · exact higmanVCTauComm_flexA_case hd hB hS hpq hqp hp hq hA h2 hF hmx hmy hxy hyx hxy' hyx'
  · exact higmanVCTauComm_flexB_case hd hB hS hpq hqp hp hq hA h2 hF hmx hmy hxy hyx hxy' hyx'
  · exact higmanVCTauComm_flip_eq hp hq (higmanVCTauComm_flexA_case hd hB hS hpq hqp hp hq hA'
      h1 hF hmx' hmy' hxy' hyx' hxy hyx)
  · exact higmanVCTauComm_flip_eq hp hq (higmanVCTauComm_flexB_case hd hB hS hpq hqp hp hq hA'
      h1 hF hmx' hmy' hxy' hyx' hxy hyx)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_easy

/-- The group identity behind the conjugated-conjugator hop:
`ℓ_s = ℓ_r ℓ_{s1} ℓ_r⁻¹` and three conjugations give the fourth. -/
theorem higmanVCTauLevel_groupC {G : Type*} [Group G] {Lr Ls Ls1 TA TA1 TB1 TB : G}
    (hL : Lr * Lr = 1) (hv : Lr * Ls * Lr⁻¹ = Ls1) (e1 : Lr * TA * Lr⁻¹ = TA1)
    (e2 : Ls1 * TA1 * Ls1⁻¹ = TB1) (e3 : Lr * TB1 * Lr⁻¹ = TB) : Ls * TA * Ls⁻¹ = TB := by
  have hi : Lr⁻¹ = Lr := inv_eq_of_mul_eq_one_right hL
  have hb : ∀ z : G, Lr * (Lr * z) = z := fun z => by rw [← mul_assoc, hL, one_mul]
  subst hv e1 e2 e3
  rw [hi, mul_inv_rev, mul_inv_rev, hi]
  simp only [mul_assoc, hb, hL, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_groupC

end GroupApproximation.BooneHigman.Metabelian.Envelope
