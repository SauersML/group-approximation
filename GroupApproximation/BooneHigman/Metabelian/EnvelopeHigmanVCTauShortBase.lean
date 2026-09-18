import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauConjFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# Short-conjugator instances for the canonical `τ`: vocabulary (lane bh-met-77j)

Vocabulary for the level induction of `EnvelopeHigmanVCTauShortReduce`:

* `higmanVCTauShort_conjEq d p q x y x' y'`: the conjugation identity
  `ψ(p, q) · ψ(x, y) · ψ(p, q)⁻¹ = ψ(x', y')` in `higmanVC_Q d` (`ψ := ψ_τ`, `τ` canonical);
* `higmanVCTauShort_Inst`: that identity under the hypotheses of a conjugation relator with a
  short conjugator (all-short instances included);
* `higmanVCTauShort_Below d n`: every instance with `|x| + |y| < n` and `|x'| + |y'| < n`;
* `higmanVCTauShort_Shrink d n`: every instance with `|x| + |y| < n` and `|x'| + |y'| ≤ n`.

Proved here: all-short instances are short relators (`higmanVCTauShort_allShort`), and an
instance can be read backwards (`higmanVCTauShort_symm`, the letter `ℓ(p, q)` is an
involution).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The conjugation identity `ψ(p, q) · ψ(x, y) · ψ(p, q)⁻¹ = ψ(x', y')`. -/
def higmanVCTauShort_conjEq (d : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)) *
      higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x, y)) *
      (higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)))⁻¹ =
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x', y'))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_conjEq

/-- A short-conjugator instance of the conjugation family. -/
def higmanVCTauShort_Inst (d : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  ∀ (hpq : ¬ p <+: q) (hqp : ¬ q <+: p), p.length ≤ 3 → q.length ≤ 3 →
    MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
    ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
    higmanVCTauShort_conjEq d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_Inst

/-- All instances strictly below level `n` on both sides. -/
def higmanVCTauShort_Below (d n : ℕ) : Prop :=
  ∀ p q x y x' y' : List (Fin d), x.length + y.length < n → x'.length + y'.length < n →
    higmanVCTauShort_Inst d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_Below

/-- All instances with source below level `n` and target at most level `n`. -/
def higmanVCTauShort_Shrink (d n : ℕ) : Prop :=
  ∀ p q x y x' y' : List (Fin d), x.length + y.length < n → x'.length + y'.length ≤ n →
    higmanVCTauShort_Inst d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_Shrink

/-- Conjugation by an involution can be undone. -/
theorem higmanVCTauShort_flip {H : Type*} [Group H] {L a b : H} (hL : L * L = 1)
    (h : L * a * L⁻¹ = b) : L * b * L⁻¹ = a := by
  have hi : L⁻¹ = L := inv_eq_of_mul_eq_one_right hL
  have ha := higmanVCTauConj_inv_conj hL h
  rw [ha, hi, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_flip

/-- Conjugation is multiplicative: conjugating `L D L⁻¹` by `g`. -/
theorem higmanVCTauShort_conj_prod {H : Type*} [Group H] {g L D L' D' G' : H}
    (h1 : g * L * g⁻¹ = L') (h2 : g * D * g⁻¹ = D') (h3 : L' * D' * L'⁻¹ = G') :
    g * (L * D * L⁻¹) * g⁻¹ = G' := by
  subst h1 h2 h3
  simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_conj_prod

/-- The image of a short generator is an involution. -/
theorem higmanVCTauShort_psi_sq (d : ℕ) {p q : List (Fin d)} (hp : p.length ≤ 3)
    (hq : q.length ≤ 3) :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)) *
        higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p, q)) = 1 := by
  rw [higmanVCTauConj_psi_letter d (p, q) ⟨hp, hq⟩]
  exact higmanVCTau_letter_sq d _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_psi_sq

/-- **All-short instances** are short conjugation relators. -/
theorem higmanVCTauShort_allShort {d : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hs : x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  unfold higmanVCTauShort_conjEq
  refine (higmanVCTauConj_rel_iff d (p, q) (x, y) (x', y')).mp ?_
  refine higmanVC_psi_short _ (by omega) ?_
  rw [higmanVC_rels, Set.mem_setOf_eq]
  exact Or.inr (Or.inr (Or.inl ⟨p, q, x, y, x', y', hp, hq, hs.1, hs.2.1, hs.2.2.1,
    hs.2.2.2, hpq, hqp, hmx, hmy, hxy, hyx, hxy', hyx', rfl⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_allShort

/-- **Symmetry.**  An instance read backwards is an instance (`(p q)` is an involution). -/
theorem higmanVCTauShort_symm {d : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauShort_Inst d p q x y x' y') : higmanVCTauShort_Inst d p q x' y' x y := by
  unfold higmanVCTauShort_Inst at h ⊢
  intro hpq hqp hp hq hmx hmy hxy hyx hxy' hyx'
  have hss := coneSwap_mul_self hpq hqp
  have e := h hpq hqp hp hq (higmanVCTauConj_mapsCone_symm hmx hss)
    (higmanVCTauConj_mapsCone_symm hmy hss) hxy' hyx' hxy hyx
  unfold higmanVCTauShort_conjEq at e ⊢
  exact higmanVCTauShort_flip (higmanVCTauShort_psi_sq d hp hq) e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_symm

end GroupApproximation.BooneHigman.Metabelian.Envelope
