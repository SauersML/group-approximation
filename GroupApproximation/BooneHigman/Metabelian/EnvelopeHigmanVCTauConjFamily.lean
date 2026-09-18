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

/-- **The induction step** for a long conjugator `(p, q)` with descent `(P, Q, X, Y)`. -/
theorem higmanVCTauConj_long_step (hS : HigmanVCTauConjShortStatement) {d : ℕ} (hd : 1 < d)
    {p q : List (Fin d)} (hlong : ¬ (p.length ≤ 3 ∧ q.length ≤ 3)) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p)
    (ih : ∀ (x y x' y' : List (Fin d))
      (hXY : ¬ higmanVCTau_pX (p, q) <+: higmanVCTau_pY (p, q))
      (hYX : ¬ higmanVCTau_pY (p, q) <+: higmanVCTau_pX (p, q)),
      MapsCone (coneSwap _ _ hXY hYX) x x' → MapsCone (coneSwap _ _ hXY hYX) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVC_psi d (higmanVCTau_tau d)
          (FreeGroup.of (higmanVCTau_pX (p, q), higmanVCTau_pY (p, q))) *
          higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x, y)) *
          (higmanVC_psi d (higmanVCTau_tau d)
            (FreeGroup.of (higmanVCTau_pX (p, q), higmanVCTau_pY (p, q))))⁻¹ =
        higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x', y')))
    {x y x' y' : List (Fin d)}
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)) *
        higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x, y)) *
        (higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)))⁻¹ =
      higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x', y')) := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨hPQ, hQP, hPl, hQl, hXp, hYq, -, hcone⟩ :=
    higmanVCTauConj_pair_descent hd hlong hpq hqp
  have hXY := higmanVCTauConj_not_prefix_of_maps hXp hYq hpq
  have hYX := higmanVCTauConj_not_prefix_of_maps hYq hXp hqp
  have hσσ := coneSwap_mul_self hPQ hQP
  have hconj := vgen_conj_coneSwap hpq hqp hXY hYX hXp hYq
  have hdσ := higmanVCTauConj_inv_conj hσσ hconj
  have hpqσ := coneSwap_mul_self hpq hqp
  have hmx' := higmanVCTauConj_mapsCone_symm hmx hpqσ
  have hmy' := higmanVCTauConj_mapsCone_symm hmy hpqσ
  obtain ⟨x1, hx1⟩ := hcone x (higmanVCTauConj_eq_of_prefix_left hpq hqp hmx)
    (higmanVCTauConj_eq_of_prefix_right hpq hqp hmx)
  obtain ⟨y1, hy1⟩ := hcone y (higmanVCTauConj_eq_of_prefix_left hpq hqp hmy)
    (higmanVCTauConj_eq_of_prefix_right hpq hqp hmy)
  obtain ⟨x2, hx2⟩ := hcone x' (higmanVCTauConj_eq_of_prefix_left hpq hqp hmx')
    (higmanVCTauConj_eq_of_prefix_right hpq hqp hmx')
  obtain ⟨y2, hy2⟩ := hcone y' (higmanVCTauConj_eq_of_prefix_left hpq hqp hmy')
    (higmanVCTauConj_eq_of_prefix_right hpq hqp hmy')
  have hx1y1 := higmanVCTauConj_not_prefix_of_maps (higmanVCTauConj_mapsCone_symm hx1 hσσ)
    (higmanVCTauConj_mapsCone_symm hy1 hσσ) hxy
  have hy1x1 := higmanVCTauConj_not_prefix_of_maps (higmanVCTauConj_mapsCone_symm hy1 hσσ)
    (higmanVCTauConj_mapsCone_symm hx1 hσσ) hyx
  have hx2y2 := higmanVCTauConj_not_prefix_of_maps (higmanVCTauConj_mapsCone_symm hx2 hσσ)
    (higmanVCTauConj_mapsCone_symm hy2 hσσ) hxy'
  have hy2x2 := higmanVCTauConj_not_prefix_of_maps (higmanVCTauConj_mapsCone_symm hy2 hσσ)
    (higmanVCTauConj_mapsCone_symm hx2 hσσ) hyx'
  have h1 := higmanVCTauConj_eq_of_shortPair hS hd hPl hQl hPQ hQP hx1 hy1 hxy hyx hx1y1 hy1x1
  have h3 := higmanVCTauConj_eq_of_shortPair hS hd hPl hQl hPQ hQP hx2 hy2 hxy' hyx' hx2y2 hy2x2
  have hdx : MapsCone (coneSwap _ _ hXY hYX) x1 x2 := by
    rw [hdσ]
    exact ((higmanVCTauConj_mapsCone_symm hx1 hσσ).comp hmx).comp hx2
  have hdy : MapsCone (coneSwap _ _ hXY hYX) y1 y2 := by
    rw [hdσ]
    exact ((higmanVCTauConj_mapsCone_symm hy1 hσσ).comp hmy).comp hy2
  have h2 := ih x1 y1 x2 y2 hXY hYX hdx hdy hx1y1 hy1x1 hx2y2 hy2x2
  have hL := higmanVCTauConj_psi_letter d (higmanVCTau_pP (p, q), higmanVCTau_pQ (p, q))
    ⟨hPl, hQl⟩
  rw [hL] at h1 h3
  rw [higmanVCTauConj_psi_of d (p, q), higmanVCTauConj_tau_descent hd hlong hpq hqp,
    ← higmanVCTauConj_psi_of d (higmanVCTau_pX (p, q), higmanVCTau_pY (p, q))]
  exact higmanVCTauConj_group (higmanVCTau_letter_sq d _) h1 h2 h3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_long_step

/-- **Induction on `|p| + |q|`.** -/
theorem higmanVCTauConj_eq_of_le (hS : HigmanVCTauConjShortStatement) {d : ℕ} (hd : 1 < d)
    (n : ℕ) :
    ∀ (p q x y x' y' : List (Fin d)), p.length + q.length ≤ n →
      ∀ (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)) *
          higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x, y)) *
          (higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)))⁻¹ =
        higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x', y')) := by
  induction n with
  | zero =>
    intro p q x y x' y' hn hpq hqp hmx hmy hxy hyx hxy' hyx'
    exact higmanVCTauConj_eq_of_shortPair hS hd (by omega) (by omega) hpq hqp hmx hmy hxy hyx
      hxy' hyx'
  | succ n ih =>
    intro p q x y x' y' hn hpq hqp hmx hmy hxy hyx hxy' hyx'
    by_cases hs : p.length ≤ 3 ∧ q.length ≤ 3
    · exact higmanVCTauConj_eq_of_shortPair hS hd hs.1 hs.2 hpq hqp hmx hmy hxy hyx hxy' hyx'
    · have hlt := higmanVCTauConj_len_lt hd hs hpq hqp
      exact higmanVCTauConj_long_step hS hd hs hpq hqp
        (fun x y x' y' hXY hYX => ih (higmanVCTau_pX (p, q)) (higmanVCTau_pY (p, q))
          x y x' y' (by omega) hXY hYX) hmx hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_eq_of_le

/-- **Reduction.**  The short-conjugator family gives the whole conjugation family. -/
theorem higmanVCTauConj_conjFamily_of_short (hS : HigmanVCTauConjShortStatement) :
    HigmanVCTauConjFamilyStatement := by
  intro d hd p q x y x' y' hpq hqp hmx hmy hxy hyx hxy' hyx'
  exact (higmanVCTauConj_rel_iff d (p, q) (x, y) (x', y')).mpr
    (higmanVCTauConj_eq_of_le hS hd (p.length + q.length) p q x y x' y' le_rfl hpq hqp hmx hmy
      hxy hyx hxy' hyx')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_conjFamily_of_short

/-- **Strength (loud): EQUIVALENT.**  The remaining gap is logically equivalent to the
target. -/
theorem higmanVCTauConj_family_iff_short :
    HigmanVCTauConjFamilyStatement ↔ HigmanVCTauConjShortStatement :=
  ⟨higmanVCTauConj_short_of_family, higmanVCTauConj_conjFamily_of_short⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_family_iff_short

end GroupApproximation.BooneHigman.Metabelian.Envelope
