import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Index
import GroupApproximation.Kazhdan.KMSGroupPresentation

/-!
# A finite quotient of `GHB(7)`: the matrices of CCKW Proposition 7.15

Caprace–Conder–Kaluba–Witzel, *Hyperbolic generalized triangle groups, property (T)
and finite simple quotients* (arXiv:2011.09276), Proposition 7.15 with block size
`k = 1` and `Ma = Mb = Mc = 1`, gives the homomorphism

```
ψ : GHB(7) → GL₄(F₇),   a ↦ I + E₀₃ + E₁₂,   b ↦ I + E₁₀ − E₂₃,   c ↦ I + E₃₁.
```

This module checks the eleven relators of `GHB(7)` on these matrices by kernel
evaluation (`decide +kernel`, which is checked by the kernel and adds no axiom), defines
`ψ`, and records that its kernel `psiKer` has finite index.  Each relator is its own
theorem, so a slow one is visible in the build log.

The matrices are unipotent (`N² = 0` for `N = V − I`), so their inverses are `I − N`;
they are given as units with those explicit inverses, which keeps every group
inverse in the relators a literal matrix.  `experiments/kms_ghb7_quotient/` is the
Python check that found these matrices.
-/

namespace GroupApproximation
namespace KMSGroup
namespace GHBQuotient

/-- The ambient matrix algebra `M₄(F₇)`. -/
abbrev Mat : Type := Matrix (Fin 4) (Fin 4) (ZMod 7)

/-- The target group `GL₄(F₇)`. -/
abbrev GL4 : Type := Matrix.GeneralLinearGroup (Fin 4) (ZMod 7)

/-- `V'a = I + E₀₃ + E₁₂`. -/
def matA : Mat := !![1, 0, 0, 1; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- `V'a⁻¹ = I − E₀₃ − E₁₂`. -/
def matAInv : Mat := !![1, 0, 0, 6; 0, 1, 6, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- `V'b = I + E₁₀ − E₂₃`. -/
def matB : Mat := !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 6; 0, 0, 0, 1]

/-- `V'b⁻¹ = I − E₁₀ + E₂₃`. -/
def matBInv : Mat := !![1, 0, 0, 0; 6, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

/-- `V'c = I + E₃₁`. -/
def matC : Mat := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 0, 1]

/-- `V'c⁻¹ = I − E₃₁`. -/
def matCInv : Mat := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 6, 0, 1]

theorem matA_mul_inv : matA * matAInv = 1 := by decide +kernel
theorem matA_inv_mul : matAInv * matA = 1 := by decide +kernel
theorem matB_mul_inv : matB * matBInv = 1 := by decide +kernel
theorem matB_inv_mul : matBInv * matB = 1 := by decide +kernel
theorem matC_mul_inv : matC * matCInv = 1 := by decide +kernel
theorem matC_inv_mul : matCInv * matC = 1 := by decide +kernel

/-- The unit `V'a`. -/
def uA : GL4 := ⟨matA, matAInv, matA_mul_inv, matA_inv_mul⟩

/-- The unit `V'b`. -/
def uB : GL4 := ⟨matB, matBInv, matB_mul_inv, matB_inv_mul⟩

/-- The unit `V'c`. -/
def uC : GL4 := ⟨matC, matCInv, matC_mul_inv, matC_inv_mul⟩

/-- The images of the three generators `a, b, c`. -/
def gens : Fin 3 → GL4 := ![uA, uB, uC]

/-! ## The eleven relators, one theorem each -/

theorem lift_a_pow : FreeGroup.lift gens (ga ^ 7) = 1 := by decide +kernel
theorem lift_b_pow : FreeGroup.lift gens (gb ^ 7) = 1 := by decide +kernel
theorem lift_c_pow : FreeGroup.lift gens (gc ^ 7) = 1 := by decide +kernel
theorem lift_aba : FreeGroup.lift gens (comm3 ga gb ga) = 1 := by decide +kernel
theorem lift_abb : FreeGroup.lift gens (comm3 ga gb gb) = 1 := by decide +kernel
theorem lift_cbc : FreeGroup.lift gens (comm3 gc gb gc) = 1 := by decide +kernel
theorem lift_cbbc : FreeGroup.lift gens (comm4 gc gb gb gc) = 1 := by decide +kernel
theorem lift_cbbb : FreeGroup.lift gens (comm4 gc gb gb gb) = 1 := by decide +kernel
theorem lift_cac : FreeGroup.lift gens (comm3 gc ga gc) = 1 := by decide +kernel
theorem lift_caac : FreeGroup.lift gens (comm4 gc ga ga gc) = 1 := by decide +kernel
theorem lift_caaa : FreeGroup.lift gens (comm4 gc ga ga ga) = 1 := by decide +kernel

/-- **All eleven relators of `GHB(7)` hold on `V'a, V'b, V'c`.** -/
theorem lift_relator_eq_one : ∀ r ∈ relators 7, FreeGroup.lift gens r = 1 := by
  intro r hr
  have hr' : r ∈ relatorList 7 := by simpa [relators] using hr
  simp only [relatorList, List.mem_cons, List.mem_nil_iff, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lift_a_pow
  · exact lift_b_pow
  · exact lift_c_pow
  · exact lift_aba
  · exact lift_abb
  · exact lift_cbc
  · exact lift_cbbc
  · exact lift_cbbb
  · exact lift_cac
  · exact lift_caac
  · exact lift_caaa

/-- **The quotient `ψ : GHB(7) → GL₄(F₇)`** of CCKW Proposition 7.15 (`k = 1`). -/
def psi : GHB 7 →* GL4 := PresentedGroup.toGroup lift_relator_eq_one

theorem psi_a : psi (a 7) = uA := PresentedGroup.toGroup.of lift_relator_eq_one (x := 0)

theorem psi_b : psi (b 7) = uB := PresentedGroup.toGroup.of lift_relator_eq_one (x := 1)

theorem psi_c : psi (c 7) = uC := PresentedGroup.toGroup.of lift_relator_eq_one (x := 2)

/-- The candidate torsion-free subgroup: the kernel of `ψ`. -/
abbrev psiKer : Subgroup (GHB 7) := psi.ker

/-- **`psiKer` has finite index**, being the kernel of a homomorphism to a finite group. -/
instance psiKer_finiteIndex : psiKer.FiniteIndex := Subgroup.finiteIndex_ker psi

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.lift_relator_eq_one
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.psi_a
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.psi_b
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.psi_c
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.psiKer_finiteIndex
