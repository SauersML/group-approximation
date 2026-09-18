import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPSplitRel
import GroupApproximation.Meta.AxiomGuard

/-!
# The all-swaps presentation of `V_d` and the short inclusion (lane bh-met-77b)

The free group on all ordered pairs of words over `Fin d` evaluates into `V_d` by
`(v, w) ↦ vgenSwapOrOne v w` (`higmanVC_evalAll`).  The standard relators `higmanVC_rels d P`
come in four families, each restricted to words satisfying a predicate `P`:

* comparable letters `(v, w)` (evaluating to `1`);
* involutions `(v, w)²`;
* conjugations `(p, q) (x, y) (p, q)⁻¹ (x', y')⁻¹`, when the cone swap `(p q)` carries the cones
  `x`, `y` onto `x'`, `y'`;
* splits `(v, w) · (∏_{a ∈ finRange d} (va, wa))⁻¹` for incomparable `v`, `w`.

They are sound (`higmanVC_rels_subset_ker`).  The short free group of lane bh-met-77 includes
into the all-swaps free group (`higmanVC_iota`) compatibly with the evaluations
(`higmanVC_evalAll_comp_iota`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Evaluation of the free group on all ordered pairs of words into `V_d`. -/
noncomputable def higmanVC_evalAll (d : ℕ) :
    FreeGroup (List (Fin d) × List (Fin d)) →* ↥(higmanThompsonV (Fin d)) :=
  FreeGroup.lift fun p => vgenSwapOrOne p.1 p.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_evalAll

/-- The generator `(v, w)` evaluates to `vgenSwapOrOne v w`. -/
theorem higmanVC_evalAll_of {d : ℕ} (v w : List (Fin d)) :
    higmanVC_evalAll d (FreeGroup.of (v, w)) = vgenSwapOrOne v w := by
  rw [higmanVC_evalAll, FreeGroup.lift_apply_of]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_evalAll_of

/-- The all-swaps split word `∏_{a ∈ finRange d} (va, wa)`. -/
def higmanVC_splitAll {d : ℕ} (v w : List (Fin d)) : FreeGroup (List (Fin d) × List (Fin d)) :=
  ((List.finRange d).map fun a => FreeGroup.of (v ++ [a], w ++ [a])).prod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_splitAll

/-- The all-swaps split word evaluates to `(v w)`. -/
theorem higmanVC_evalAll_splitAll {d : ℕ} {v w : List (Fin d)} (h1 : ¬ v <+: w)
    (h2 : ¬ w <+: v) :
    ((higmanVC_evalAll d (higmanVC_splitAll v w) : ↥(higmanThompsonV (Fin d))) :
      Equiv.Perm (Cantor (Fin d))) = coneSwap v w h1 h2 :=
  (higmanVFP_coe_map_list_prod (higmanVC_evalAll d)
      (fun a => FreeGroup.of (v ++ [a], w ++ [a])) (higmanVFPSplitSwap h1 h2)
      (fun a => congrArg Subtype.val ((higmanVC_evalAll_of (v ++ [a]) (w ++ [a])).trans
        (vgenSwapOrOne_eq (higmanVFP_ext_incomp h1 h2 a a) (higmanVFP_ext_incomp h2 h1 a a))))
      (List.finRange d)).trans
    (higmanVFP_splitProd_eq h1 h2 (List.finRange d) (List.nodup_finRange d) List.mem_finRange)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_evalAll_splitAll

/-- The standard relators of the all-swaps presentation whose words all satisfy `P`. -/
def higmanVC_rels (d : ℕ) (P : List (Fin d) → Prop) :
    Set (FreeGroup (List (Fin d) × List (Fin d))) :=
  {t | (∃ v w : List (Fin d), P v ∧ P w ∧ ¬ (¬ v <+: w ∧ ¬ w <+: v) ∧
        t = FreeGroup.of (v, w)) ∨
      (∃ v w : List (Fin d), P v ∧ P w ∧ t = FreeGroup.of (v, w) * FreeGroup.of (v, w)) ∨
      (∃ p q x y x' y' : List (Fin d), P p ∧ P q ∧ P x ∧ P y ∧ P x' ∧ P y' ∧
        ∃ (hpq : ¬ p <+: q) (hqp : ¬ q <+: p), MapsCone (coneSwap p q hpq hqp) x x' ∧
          MapsCone (coneSwap p q hpq hqp) y y' ∧ ¬ x <+: y ∧ ¬ y <+: x ∧ ¬ x' <+: y' ∧
          ¬ y' <+: x' ∧
          t = FreeGroup.of (p, q) * FreeGroup.of (x, y) * (FreeGroup.of (p, q))⁻¹ *
            (FreeGroup.of (x', y'))⁻¹) ∨
      (∃ v w : List (Fin d), P v ∧ P w ∧ (∀ a, P (v ++ [a]) ∧ P (w ++ [a])) ∧ ¬ v <+: w ∧
        ¬ w <+: v ∧ t = FreeGroup.of (v, w) * (higmanVC_splitAll v w)⁻¹)}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_rels

/-- **Soundness.**  The standard relators lie in the kernel of the evaluation. -/
theorem higmanVC_rels_subset_ker (d : ℕ) (P : List (Fin d) → Prop) :
    higmanVC_rels d P ⊆ (higmanVC_evalAll d).ker := by
  intro t ht
  refine MonoidHom.mem_ker.mpr ?_
  rcases ht with ⟨v, w, _, _, hc, rfl⟩ | ⟨v, w, _, _, rfl⟩ |
      ⟨p, q, x, y, x', y', _, _, _, _, _, _, hpq, hqp, hmx, hmy, hxy, hyx, hxy', hyx', rfl⟩ |
      ⟨v, w, _, _, _, h1, h2, rfl⟩
  · rw [higmanVC_evalAll_of]
    exact higmanVFP_swapOrOne_of_not hc
  · rw [map_mul, higmanVC_evalAll_of]
    exact higmanVFP_swapOrOne_mul_self v w
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, higmanVC_evalAll_of, higmanVC_evalAll_of,
      higmanVC_evalAll_of]
    exact higmanVFP_swapOrOne_conj hpq hqp hxy hyx hxy' hyx' hmx hmy
  · rw [map_mul, map_inv, mul_inv_eq_one, higmanVC_evalAll_of, vgenSwapOrOne_eq h1 h2]
    exact Subtype.ext (higmanVC_evalAll_splitAll h1 h2).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_rels_subset_ker

/-- The inclusion of the short free group of lane bh-met-77 into the all-swaps free group. -/
noncomputable def higmanVC_iota (d : ℕ) :
    FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d)))) →*
      FreeGroup (List (Fin d) × List (Fin d)) :=
  FreeGroup.lift fun i => FreeGroup.of ((vgenShortEquiv (Fin d)).symm i).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_iota

/-- The inclusion is compatible with the two evaluations. -/
theorem higmanVC_evalAll_comp_iota (d : ℕ) :
    (higmanVC_evalAll d).comp (higmanVC_iota d) = FreeGroup.lift (vgenShortSwaps (Fin d)) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp only [MonoidHom.comp_apply, higmanVC_iota, higmanVC_evalAll, FreeGroup.lift_apply_of,
    vgenShortSwaps]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_evalAll_comp_iota

end GroupApproximation.BooneHigman.Metabelian.Envelope
