import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauSplitDescent
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The canonical `τ` kills every split relator (lane bh-met-77f)

**Split family** (`higmanVCTauSplit_split`): for `T := higmanVCTau_tau d` and `1 < d`,
`ψ_T` kills `(v, w) * (∏ₐ (v a, w a))⁻¹` for every incomparable pair of words of any length.

Proof: `ψ_T (of p) = T p`, so the claim is `T (v, w) = ∏ₐ T (v a, w a)`, by induction on
`|v| + |w|`.  Short pairs (`|v|, |w| ≤ 2`): the short split relator (`higmanVC_psi_short`).
Otherwise the generalized descent identity writes `T (v, w)` as the `T (P, Q)`-conjugate of
`T (X, Y)` with `|X| + |Y| < |v| + |w|`; by induction `T (X, Y) = ∏ₐ T (X a, Y a)`,
conjugation distributes over the product, and appending `a` fixes `P`, `Q` and appends `a` to
`X`, `Y`, so each factor is `T (v a, w a)` by the descent identity for `(v a, w a)`.

**Reduction** (`higmanVCTauSplit_conjSplit_of_conj`): the remaining gap
`HigmanVCTauConjSplitStatement` of lane bh-met-77e follows from its conjugation conjunct alone,
`HigmanVCTauConjStatement` (strictly less: it is literally one conjunct of the gap, the other
conjunct being proved here).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Conjugation distributes over a list product. -/
theorem higmanVCTauSplit_prod_conj {G : Type*} [Group G] {α : Type*} (g : G) (f : α → G)
    (l : List α) : (l.map fun a => g * f a * g⁻¹).prod = g * (l.map f).prod * g⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ih]
    simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_prod_conj

/-- `ψ_T` of the all-swaps split word is the product of the canonical values. -/
theorem higmanVCTauSplit_psi_splitAll (d : ℕ) (v w : List (Fin d)) :
    higmanVC_psi d (higmanVCTau_tau d) (higmanVC_splitAll v w) =
      ((List.finRange d).map fun a => higmanVCTau_tau d (v ++ [a], w ++ [a])).prod := by
  rw [higmanVC_splitAll, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun a _ => ?_)
  exact higmanVCTauSplit_psi_of d (v ++ [a], w ++ [a])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_psi_splitAll

/-- Base case: the short split relator. -/
theorem higmanVCTauSplit_base {d : ℕ} (hd : 1 < d) {v w : List (Fin d)} (hvw : ¬ v <+: w)
    (hwv : ¬ w <+: v) (hv : v.length ≤ 2) (hw : w.length ≤ 2) :
    higmanVCTau_tau d (v, w) =
      ((List.finRange d).map fun a => higmanVCTau_tau d (v ++ [a], w ++ [a])).prod := by
  have hmem : FreeGroup.of (v, w) * (higmanVC_splitAll v w)⁻¹ ∈
      higmanVC_rels d fun l => l.length ≤ 3 := by
    rw [higmanVC_rels, Set.mem_setOf_eq]
    exact Or.inr (Or.inr (Or.inr ⟨v, w, higmanVFP_len_le3 hv, higmanVFP_len_le3 hw,
      fun a => ⟨higmanVFP_len_succ hv a, higmanVFP_len_succ hw a⟩, hvw, hwv, rfl⟩))
  have h' := higmanVC_psi_short (higmanVCTau_tau d) (by omega : 0 < d) hmem
  rw [map_mul, map_inv, mul_inv_eq_one, higmanVCTauSplit_psi_of,
    higmanVCTauSplit_psi_splitAll] at h'
  exact h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_base

/-- Induction step: the split identity for the descended pair gives it for `(v, w)`. -/
theorem higmanVCTauSplit_step {d : ℕ} (hd : 1 < d) {v w : List (Fin d)} (hvw : ¬ v <+: w)
    (hwv : ¬ w <+: v) (hs : ¬ (v.length ≤ 2 ∧ w.length ≤ 2))
    (ih : higmanVCTau_tau d (higmanVCTau_pX (v, w), higmanVCTau_pY (v, w)) =
      ((List.finRange d).map fun a =>
        higmanVCTau_tau d (higmanVCTau_pX (v, w) ++ [a], higmanVCTau_pY (v, w) ++ [a])).prod) :
    higmanVCTau_tau d (v, w) =
      ((List.finRange d).map fun a => higmanVCTau_tau d (v ++ [a], w ++ [a])).prod := by
  have hpt : ∀ a ∈ List.finRange d,
      higmanVCTau_tau d (higmanVCTau_pP (v, w), higmanVCTau_pQ (v, w)) *
          higmanVCTau_tau d (higmanVCTau_pX (v, w) ++ [a], higmanVCTau_pY (v, w) ++ [a]) *
            (higmanVCTau_tau d (higmanVCTau_pP (v, w), higmanVCTau_pQ (v, w)))⁻¹ =
        higmanVCTau_tau d (v ++ [a], w ++ [a]) := by
    intro a _
    obtain ⟨e1, e2, e3, e4⟩ := higmanVCTauSplit_pair_append hvw hwv hs a
    have hs' : ¬ ((v ++ [a]).length ≤ 2 ∧ (w ++ [a]).length ≤ 2) := by
      rw [List.length_append, List.length_append, List.length_singleton]
      omega
    rw [higmanVCTauSplit_descent hd (higmanVFP_ext_incomp hvw hwv a a)
      (higmanVFP_ext_incomp hwv hvw a a) hs', e1, e2, e3, e4]
  rw [higmanVCTauSplit_descent hd hvw hwv hs, ih, ← higmanVCTauSplit_prod_conj]
  exact congrArg List.prod (List.map_congr_left hpt)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_step

/-- The split identity `T (v, w) = ∏ₐ T (v a, w a)`, by induction on `|v| + |w|`. -/
theorem higmanVCTauSplit_core {d : ℕ} (hd : 1 < d) :
    ∀ n : ℕ, ∀ v w : List (Fin d), v.length + w.length ≤ n → ¬ v <+: w → ¬ w <+: v →
      higmanVCTau_tau d (v, w) =
        ((List.finRange d).map fun a => higmanVCTau_tau d (v ++ [a], w ++ [a])).prod := by
  intro n
  induction n with
  | zero =>
    intro v w hn hvw hwv
    exact higmanVCTauSplit_base hd hvw hwv (by omega) (by omega)
  | succ n ih =>
    intro v w hn hvw hwv
    by_cases hs : v.length ≤ 2 ∧ w.length ≤ 2
    · exact higmanVCTauSplit_base hd hvw hwv hs.1 hs.2
    · obtain ⟨hxy, hyx⟩ := higmanVCTauSplit_pair_incomp hd hvw hwv hs
      have hl := higmanVCTauSplit_pair_len hd hvw hwv hs
      exact higmanVCTauSplit_step hd hvw hwv hs (ih _ _ (by omega) hxy hyx)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_core

/-- **Split family.**  For the canonical `τ`, `ψ_τ` kills every split relator. -/
theorem higmanVCTauSplit_split (d : ℕ) (hd : 1 < d) (v w : List (Fin d)) (hvw : ¬ v <+: w)
    (hwv : ¬ w <+: v) :
    higmanVC_psi d (higmanVCTau_tau d)
      (FreeGroup.of (v, w) * (higmanVC_splitAll v w)⁻¹) = 1 := by
  rw [map_mul, map_inv, mul_inv_eq_one, higmanVCTauSplit_psi_of, higmanVCTauSplit_psi_splitAll]
  exact higmanVCTauSplit_core hd _ v w le_rfl hvw hwv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_split

/-- **Remaining gap (conjugation family).**  For the canonical `τ`, `ψ_τ` kills every
conjugation relator; exactly the first conjunct of `HigmanVCTauConjSplitStatement`. -/
def HigmanVCTauConjStatement : Prop :=
  ∀ d : ℕ, 1 < d →
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVC_psi d (higmanVCTau_tau d)
        (FreeGroup.of (p, q) * FreeGroup.of (x, y) * (FreeGroup.of (p, q))⁻¹ *
          (FreeGroup.of (x', y'))⁻¹) = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauConjStatement

/-- **Reduction.**  The conjugation family alone gives the gap of lane bh-met-77e. -/
theorem higmanVCTauSplit_conjSplit_of_conj (h : HigmanVCTauConjStatement) :
    HigmanVCTauConjSplitStatement :=
  fun d hd => ⟨h d hd, fun v w hvw hwv => higmanVCTauSplit_split d hd v w hvw hwv⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_conjSplit_of_conj

/-- **Reduction to `hB`.**  The conjugation family alone gives `HigmanVCTauStatement`. -/
theorem higmanVCTauSplit_tau_of_conj (h : HigmanVCTauConjStatement) : HigmanVCTauStatement :=
  higmanVCTau_of_conjSplit (higmanVCTauSplit_conjSplit_of_conj h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_tau_of_conj

end GroupApproximation.BooneHigman.Metabelian.Envelope
