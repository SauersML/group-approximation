import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group
import Mathlib.Data.Fintype.Card
import GroupApproximation.Meta.AxiomGuard

/-!
# Pure group identities for the affine presentation (lane bh-met-05)

Research node `affine-extension-of-fp-elementary-group-is-fp-proof`, steps B and F1 of the
presentation argument (`research/artifacts/bh-sl3-zt-host-2026-09-12.md`, §2).  These are the
word identities used there, stated for arbitrary elements of an arbitrary group:

* `commute_commutator_of`: an element commuting with `g` and `t` commutes with `⁅g, t⁆`;
* `commute_of_shear` (step B, case `l = k`): the "shear" conjugation `h s h⁻¹ = s t` forces
  `t` to commute with `⁅g, t⁆`;
* `mul_commutator_eq_one` (step F1): conjugating the commuting pair `(b, c)` by `u` gives
  `⁅b, d⁆ ⁅a, c⁆ = 1`;
* `exists_ne_three`: with at least four indices one avoids any three.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace AffineFP

open scoped commutatorElement

section Group

variable {P : Type*} [Group P]

/-- An element commuting with `g` and `t` commutes with their commutator. -/
theorem commute_commutator_of {c g t : P} (hg : Commute c g) (ht : Commute c t) :
    Commute c ⁅g, t⁆ := by
  rw [commutatorElement_def]
  exact ((hg.mul_right ht).mul_right hg.inv_right).mul_right ht.inv_right

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.commute_commutator_of

/-- Step B of the presentation argument, as a pure word identity.  If `s` commutes with `g`
and `t`, `h` conjugates `s` to `s t`, fixes `t`, and conjugates `g` to `c g` for some `c`
commuting with `g` and `t`, then `t` commutes with `⁅g, t⁆`. -/
theorem commute_of_shear {g t s h c : P} (hsg : Commute s g) (hst : Commute s t)
    (hhs : h * s * h⁻¹ = s * t) (hht : h * t * h⁻¹ = t) (hhg : h * g * h⁻¹ = c * g)
    (hcg : Commute c g) (hct : Commute c t) : Commute t ⁅g, t⁆ := by
  have hY : Commute s (g * t * g⁻¹) := (hsg.mul_right hst).mul_right hsg.inv_right
  have hcY : Commute c (g * t * g⁻¹) := (hcg.mul_right hct).mul_right hcg.inv_right
  have hconj : h * (g * t * g⁻¹) * h⁻¹ = g * t * g⁻¹ := by
    calc h * (g * t * g⁻¹) * h⁻¹
        = (h * g * h⁻¹) * (h * t * h⁻¹) * (h * g * h⁻¹)⁻¹ := by group
      _ = c * (g * t * g⁻¹) * c⁻¹ := by rw [hhg, hht]; group
      _ = g * t * g⁻¹ := hcY.mul_inv_cancel
  have h2 : Commute (s * t) (g * t * g⁻¹) := by
    have := hY.map (MulAut.conj h)
    rw [MulAut.conj_apply, MulAut.conj_apply, hhs, hconj] at this
    exact this
  have ht : Commute t (g * t * g⁻¹) := by
    have := hY.inv_left.mul_left h2
    rwa [inv_mul_cancel_left] at this
  rw [commutatorElement_def]
  exact ht.mul_right (Commute.refl t).inv_right

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.commute_of_shear

/-- Step F1 of the presentation argument, as a pure word identity.  Conjugating the commuting
pair `(b, c)` by `u`, where `u b u⁻¹ = a b` and `u c u⁻¹ = c d`, gives `⁅b, d⁆ ⁅a, c⁆ = 1`,
provided `a` commutes with `b` and `d`, and `c` commutes with `⁅b, d⁆`. -/
theorem mul_commutator_eq_one {a b c d u : P} (hbc : Commute b c)
    (hub : u * b * u⁻¹ = a * b) (huc : u * c * u⁻¹ = c * d) (hab : Commute a b)
    (had : Commute a d) (hcY : Commute c ⁅b, d⁆) : ⁅b, d⁆ * ⁅a, c⁆ = 1 := by
  have h1 : Commute (a * b) (c * d) := by
    have := hbc.map (MulAut.conj u)
    rwa [MulAut.conj_apply, MulAut.conj_apply, hub, huc] at this
  have haY : Commute a ⁅b, d⁆ := commute_commutator_of hab had
  have e : ⁅a * b, c * d⁆ =
      a * (⁅b, c⁆ * (c * ⁅b, d⁆ * c⁻¹)) * a⁻¹ * (⁅a, c⁆ * (c * ⁅a, d⁆ * c⁻¹)) := by
    simp only [commutatorElement_def]
    group
  rw [hbc.commutator_eq, had.commutator_eq, one_mul, mul_one, mul_inv_cancel, mul_one,
    hcY.mul_inv_cancel, haY.mul_inv_cancel, h1.commutator_eq] at e
  exact e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.mul_commutator_eq_one

end Group

/-- With at least four indices, any three indices can be avoided. -/
theorem exists_ne_three {I : Type*} [Fintype I] [DecidableEq I] (hI : 4 ≤ Fintype.card I)
    (a b c : I) : ∃ d, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  by_contra hcon
  have hsub : (Finset.univ : Finset I) ⊆ {a, b, c} := by
    intro d _
    by_cases ha : d = a
    · rw [ha]
      exact Finset.mem_insert_self _ _
    by_cases hb : d = b
    · rw [hb]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hc : d = c := by
      by_contra hc
      exact hcon ⟨d, ha, hb, hc⟩
    rw [hc]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have h3 := (Finset.card_le_card hsub).trans Finset.card_le_three
  rw [Finset.card_univ] at h3
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.exists_ne_three

end AffineFP
end Metabelian
end BooneHigman
end GroupApproximation
