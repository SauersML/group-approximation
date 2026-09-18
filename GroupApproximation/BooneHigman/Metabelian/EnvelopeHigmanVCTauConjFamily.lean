import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauConjFuel
import GroupApproximation.Meta.AxiomGuard

/-!
# The conjugation family for the canonical `τ`: reduction to short conjugators (bh-met-77g)

`HigmanVCTauConjFamilyStatement` is verbatim conjunct (a) of `HigmanVCTauConjSplitStatement`
(lane bh-met-77e): for `τ := higmanVCTau_tau d`, `ψ_τ` kills every conjugation relator
`(p, q) (x, y) (p, q)⁻¹ (x', y')⁻¹`.  (It is also verbatim `HigmanVCTauConjStatement` of lane
bh-met-77f; that module is not imported here.)

**Reduction** (`higmanVCTauConj_conjFamily_of_short`): the family follows from
`HigmanVCTauConjShortStatement`, its instances with a *short* conjugator (`|p|, |q| ≤ 3`) and
some long word among `x, y, x', y'`.  Proof: induction on `|p| + |q|`.  All-short instances
are the short relators (`higmanVC_psi_short`).  For a long conjugator, the descent `(P, Q, X, Y)`
of `(p, q)` gives `τ (p, q) = ℓ · τ (X, Y) · ℓ⁻¹` with `ℓ := ℓ(P, Q)`, `ℓ² = 1`
(`higmanVCTauConj_tau_descent`) and `(p q) = (P Q) (X Y) (P Q)` (`vgen_conj_coneSwap`).  `x`
is not a proper prefix of `p`, `q` (`higmanVCTauConj_eq_of_prefix_left`/`_right`), so `(P Q)`
carries `x ↦ x₁`, `y ↦ y₁`, `x' ↦ x₂`, `y' ↦ y₂`; then `(X Y)` carries `x₁ ↦ x₂`,
`y₁ ↦ y₂`.  The two short-conjugator instances for `(P, Q)` and the induction hypothesis for
`(X, Y)` (`|X| + |Y| < |p| + |q|`) combine by `higmanVCTauConj_group`.

**Strength (loud).** `HigmanVCTauConjShortStatement` is logically **EQUIVALENT** to the
family (`higmanVCTauConj_family_iff_short`): it is a special case of it, and the reduction
gives the converse.  It is *smaller in proof content*: every instance with a long conjugator
and every all-short instance is discharged.

**Truth.** The short statement is a special case of the family, which is true by the argument
of lane bh-met-77e (from `HigmanVFPShortCompleteStatement`).  The word facts used in the
reduction were machine-checked before being proved (scratch `check.py`, `d = 2, 3`, 15560 long
incomparable pairs, 0 failures).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Target.**  Conjunct (a) of `HigmanVCTauConjSplitStatement`: for the canonical `τ`, `ψ_τ`
kills every conjugation relator. -/
def HigmanVCTauConjFamilyStatement : Prop :=
  ∀ d : ℕ, 1 < d →
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVC_psi d (higmanVCTau_tau d)
        (FreeGroup.of (p, q) * FreeGroup.of (x, y) * (FreeGroup.of (p, q))⁻¹ *
          (FreeGroup.of (x', y'))⁻¹) = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauConjFamilyStatement

/-- The family is conjunct (a) of the gap of lane bh-met-77e. -/
theorem higmanVCTauConj_family_of_conjSplit (h : HigmanVCTauConjSplitStatement) :
    HigmanVCTauConjFamilyStatement :=
  fun d hd => (h d hd).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_family_of_conjSplit

/-- **Remaining gap.**  The conjugation family for a short conjugator `(p, q)` (`|p|, |q| ≤ 3`)
and some long word among `x, y, x', y'`.  **Equivalent** to the family
(`higmanVCTauConj_family_iff_short`). -/
def HigmanVCTauConjShortStatement : Prop :=
  ∀ d : ℕ, 1 < d →
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      p.length ≤ 3 → q.length ≤ 3 →
      ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3) →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVC_psi d (higmanVCTau_tau d)
        (FreeGroup.of (p, q) * FreeGroup.of (x, y) * (FreeGroup.of (p, q))⁻¹ *
          (FreeGroup.of (x', y'))⁻¹) = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauConjShortStatement

/-- The short statement is a special case of the family. -/
theorem higmanVCTauConj_short_of_family (h : HigmanVCTauConjFamilyStatement) :
    HigmanVCTauConjShortStatement :=
  fun d hd p q x y x' y' hpq hqp _ _ _ hmx hmy hxy hyx hxy' hyx' =>
    h d hd p q x y x' y' hpq hqp hmx hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_short_of_family

/-- The conjugation identity for a short conjugator (all-short instances included). -/
theorem higmanVCTauConj_eq_of_shortPair (hS : HigmanVCTauConjShortStatement) {d : ℕ}
    (hd : 1 < d) {p q x y x' y' : List (Fin d)} (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)) *
        higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x, y)) *
        (higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)))⁻¹ =
      higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x', y')) := by
  refine (higmanVCTauConj_rel_iff d (p, q) (x, y) (x', y')).mp ?_
  by_cases hs : x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3
  · refine higmanVC_psi_short _ (by omega) ?_
    rw [higmanVC_rels, Set.mem_setOf_eq]
    exact Or.inr (Or.inr (Or.inl ⟨p, q, x, y, x', y', hp, hq, hs.1, hs.2.1, hs.2.2.1,
      hs.2.2.2, hpq, hqp, hmx, hmy, hxy, hyx, hxy', hyx', rfl⟩))
  · exact hS d hd p q x y x' y' hpq hqp hp hq hs hmx hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_eq_of_shortPair
