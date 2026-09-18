import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Conj
import GroupApproximation.Meta.AxiomGuard

/-!
# Commutators of integer powers in a class-two pair (bh-met-91f)

If `⁅g, h⁆ = c` and `c` commutes with both `g` and `h`, then `⁅g ^ a, h ^ b⁆ = c ^ (a * b)`
for all integers `a, b` (`czSLFourFP_commutator_zpow_zpow`).  This is the only group-theoretic
input of the finite presentation of `St_I(ℤ)` in `ElemFPCharZeroSLFourFPIntPres`: it shows that
`xᵢⱼ(a) ↦ yᵢⱼ ^ a` respects the adjacent Steinberg relation.

The proof applies `czSLFourFP_conj_zpow_of_conj` twice: first to conjugation by `g`, then to
conjugation by `(h ^ b)⁻¹`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- If `x y x⁻¹ = e y` and `e` commutes with `y`, then `x yⁿ x⁻¹ = eⁿ yⁿ`. -/
theorem czSLFourFP_conj_zpow_of_conj {x y e : G} (hxy : x * y * x⁻¹ = e * y)
    (hey : Commute e y) (n : ℤ) : x * y ^ n * x⁻¹ = e ^ n * y ^ n := by
  rw [← conj_zpow, hxy, hey.mul_zpow]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_conj_zpow_of_conj

/-- **Class-two commutator of powers.**  If `⁅g, h⁆ = c` with `c` commuting with `g` and `h`,
then `⁅g ^ a, h ^ b⁆ = c ^ (a * b)`. -/
theorem czSLFourFP_commutator_zpow_zpow {g h c : G} (hc : ⁅g, h⁆ = c)
    (hgc : Commute g c) (hhc : Commute h c) (a b : ℤ) :
    ⁅g ^ a, h ^ b⁆ = c ^ (a * b) := by
  have h1 : g * h * g⁻¹ = c * h := by
    rw [← hc, commutatorElement_def, inv_mul_cancel_right]
  have h2 : g * h ^ b * g⁻¹ = c ^ b * h ^ b := czSLFourFP_conj_zpow_of_conj h1 hhc.symm b
  have hdk : Commute (c ^ b) (h ^ b) := hhc.symm.zpow_zpow b b
  have h2' : g * h ^ b = c ^ b * h ^ b * g := by
    rw [← h2, inv_mul_cancel_right]
  have h3 : (h ^ b)⁻¹ * g * (h ^ b)⁻¹⁻¹ = c ^ b * g := by
    rw [inv_inv, mul_assoc, h2', hdk.eq, ← mul_assoc, inv_mul_cancel_left]
  have hdg : Commute (c ^ b) g := hgc.symm.zpow_left b
  have h4 := czSLFourFP_conj_zpow_of_conj h3 hdg a
  rw [inv_inv] at h4
  have h5 : g ^ a * h ^ b = h ^ b * ((c ^ b) ^ a * g ^ a) := by
    rw [← h4, mul_assoc, mul_inv_cancel_left]
  have hDK : Commute ((c ^ b) ^ a) (h ^ b) := hdk.zpow_left a
  calc ⁅g ^ a, h ^ b⁆ = g ^ a * h ^ b * (g ^ a)⁻¹ * (h ^ b)⁻¹ := commutatorElement_def _ _
    _ = h ^ b * (c ^ b) ^ a * (h ^ b)⁻¹ := by
      rw [h5, ← mul_assoc, mul_inv_cancel_right]
    _ = (c ^ b) ^ a := by
      rw [← hDK.eq, mul_inv_cancel_right]
    _ = c ^ (a * b) := by
      rw [← zpow_mul, mul_comm b a]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_commutator_zpow_zpow

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
