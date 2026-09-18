import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarNormConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Two group-theoretic lemmas for the `D`-words

Lane `bh-met-92u`, group module.  In any group:

* `k2KarRel_comm_swap`: if `e` and `g` commute and `⁅e, f⁆` commutes with `⁅f, g⁆`, then
  `⁅⁅e, f⁆, g⁆ = ⁅⁅f, g⁆⁻¹, e⁆`.  Proof: `g ⁅e, f⁆ g⁻¹ = ⁅e, ⁅f, g⁆⁻¹ f⁆`, and the commuting
  hypothesis rewrites this as `e ⁅f, g⁆⁻¹ e⁻¹ · ⁅f, g⁆ ⁅e, f⁆`.
* `k2KarRel_commute_of_conj`: `b a b⁻¹ = a → Commute a b`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement

section KarRelGroup

variable {G : Type*} [Group G]

/-- **Swap lemma.**  If `e g = g e` and `⁅e, f⁆` commutes with `⁅f, g⁆`, then
`⁅⁅e, f⁆, g⁆ = ⁅⁅f, g⁆⁻¹, e⁆`. -/
theorem k2KarRel_comm_swap {e f g : G} (heg : e * g = g * e)
    (hxy : ⁅e, f⁆ * ⁅f, g⁆ = ⁅f, g⁆ * ⁅e, f⁆) :
    ⁅⁅e, f⁆, g⁆ = ⁅⁅f, g⁆⁻¹, e⁆ := by
  have hge : g * e * g⁻¹ = e := by rw [← heg, mul_inv_cancel_right]
  have hgf : g * f * g⁻¹ = ⁅f, g⁆⁻¹ * f := by
    simp only [commutatorElement_def]
    group
  have h1 := k2KarNorm_conj_commutator g e f
  rw [hge, hgf] at h1
  have key : g * ⁅e, f⁆ * g⁻¹ = e * ⁅f, g⁆⁻¹ * e⁻¹ * (⁅f, g⁆ * ⁅e, f⁆) := by
    rw [h1, ← hxy]
    simp only [commutatorElement_def]
    group
  calc ⁅⁅e, f⁆, g⁆ = ⁅e, f⁆ * (g * ⁅e, f⁆ * g⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅⁅f, g⁆⁻¹, e⁆ := by
        rw [key]
        simp only [commutatorElement_def]
        group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_comm_swap

/-- If conjugation by `b` fixes `a`, then `a` and `b` commute. -/
theorem k2KarRel_commute_of_conj {a b : G} (h : b * a * b⁻¹ = a) : Commute a b := by
  have e : a * b = b * a := by
    calc a * b = b * a * b⁻¹ * b := by rw [h]
      _ = b * a := by group
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_commute_of_conj

end KarRelGroup

end GroupApproximation.BooneHigman.Metabelian.ElemFP
