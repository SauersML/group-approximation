import GroupApproximation.Sofic.LiteralAffineCongruenceBase

/-!
# Torsion-freeness of the affine congruence base

This module isolates the algebraic torsion argument from the independent
finite-presentation and property-`(T)` developments.
-/

namespace GroupApproximation
namespace LiteralAffineCongruenceBase

open LiteralNonMFPresentation
open LiteralBaseRelations
open LiteralBaseRotationRetract
open LiteralBaseTranslationNormal
open LiteralBaseTranslationLattice
open LiteralP13MatrixModel
open CongruenceSubgroup

noncomputable section

/-- The integral translation lattice is torsion-free. -/
theorem lattice_isPowerTorsionFree :
    IsPowerTorsionFree (Multiplicative Lattice) := by
  intro a n hn hpow
  apply Multiplicative.toAdd.injective
  funext i
  have hi := congrArg (fun z : Multiplicative Lattice ↦ z.toAdd i) hpow
  simp only [toAdd_pow, toAdd_one, Pi.zero_apply, nsmul_eq_mul] at hi
  rcases mul_eq_zero.mp hi with hn0 | hai
  · exact absurd (Int.natCast_eq_zero.mp hn0) hn.ne'
  · exact hai

/-- The literal translation subgroup is torsion-free. -/
theorem translations_isPowerTorsionFree : IsPowerTorsionFree translations :=
  IsPowerTorsionFree.comap lattice_isPowerTorsionFree
    latticeEquivTranslations.symm.toMonoidHom
    latticeEquivTranslations.symm.injective

/-- The affine level-three subgroup is torsion-free. A torsion element has
trivial image in `Γ(3)`, hence lies in the integral translation lattice. -/
theorem p_isPowerTorsionFree : IsPowerTorsionFree P := by
  intro g n hn hpow
  have hglinear : linearPart (g : Base) ∈ gamma3 := g.property
  let r : ↑gamma3 := ⟨linearPart g, hglinear⟩
  have hgpow : ((g : Base) ^ n) = 1 := congrArg Subtype.val hpow
  have hrpow : r ^ n = 1 := by
    apply Subtype.ext
    simpa [r] using congrArg linearPart hgpow
  have hrone : r = 1 := gamma3_torsionFree r n hn hrpow
  have hlin : linearPart (g : Base) = 1 := congrArg Subtype.val hrone
  have hrot : baseToRotation (g : Base) = 1 := by
    apply rotationEquivSL3.injective
    simpa [linearPart] using hlin
  have hgtrans : (g : Base) ∈ translations := by
    rw [← baseToRotation_ker_eq_translations, MonoidHom.mem_ker]
    exact hrot
  let t : translations := ⟨g, hgtrans⟩
  have htpow : t ^ n = 1 := by
    apply Subtype.ext
    exact hgpow
  have htone : t = 1 := translations_isPowerTorsionFree t n hn htpow
  apply Subtype.ext
  exact congrArg Subtype.val htone

end

end LiteralAffineCongruenceBase
end GroupApproximation
