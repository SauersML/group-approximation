import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTAction
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.ProperCrossedProductIdeal
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.ProperCrossedProductSaturation

/-!
# The HKT action preserves the ideals of invariant sets

Lane TWWUCT-E (WO-TWWUCT-E), manuscript label `thm:fixed-radical-membership` (UCT input,
`non_mf_group_notes.tex` L1370--1378).  Higson--Kasparov (Invent. Math. 144 (2001), §9) and
Tu (K-Theory 17 (1999), Prop. 10.7) exhaust `A(H) ⋊_r G` by the crossed products `I_{W_n} ⋊_r G`
of the ideals `I_{W_n} ⊆ A(H)` attached to the invariant open sets `W_n`.  For this they need the
action `α` of `G` on `A(H)` to preserve each `I_{W_n}`.  This file proves that.

* `AffineIsometricAction.hktAction_mem_hktIdeal`: `α_g (I_W) ⊆ I_W` for invariant `W`.
* `AffineIsometricAction.hktAction_mem_hktIdeal_exhaustion`: the same for the exhaustion `W_n`.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe u v w

namespace AffineIsometricAction

variable {G : Type u} [Group G] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (b : AffineIsometricAction G H)
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- **The HKT action preserves `I_W` for invariant `W`**: if `W ⊆ ℝ × H` is invariant under
`(t, h) ↦ (t, g • h)`, then `α_g` maps the ideal `I_W` of `A(H)` into itself
(`thm:fixed-radical-membership`, UCT input; Higson--Kasparov 2001, §9). -/
theorem hktAction_mem_hktIdeal {W : Set (ℝ × H)} (hW : b.lineAction.IsInvariantSet W) (g : G)
    {f : HKTAlgebraOf H C} (hf : f ∈ hktIdeal C W) : b.hktAction C g f ∈ hktIdeal C W := by
  have hf' : VanishesOff W f := mem_hktIdeal.1 hf
  refine mem_hktIdeal.2 fun x hx => ?_
  exact b.ambientMap_eq_zero_of_notMem hW g hf' x hx

/-- **The HKT action preserves the exhaustion ideals** `I_{W_n}`, where
`W_n = G · ⋃_{i<n} V i` (`thm:fixed-radical-membership`, UCT input; Tu 1999, §10). -/
theorem hktAction_mem_hktIdeal_exhaustion (V : ℕ → Set (ℝ × H)) (n : ℕ) (g : G)
    {f : HKTAlgebraOf H C} (hf : f ∈ hktIdeal C (b.lineAction.exhaustion V n)) :
    b.hktAction C g f ∈ hktIdeal C (b.lineAction.exhaustion V n) :=
  b.hktAction_mem_hktIdeal (b.lineAction.isInvariantSet_exhaustion V n) g hf

end AffineIsometricAction

end

end GroupApproximation.Full.TWWUCT
