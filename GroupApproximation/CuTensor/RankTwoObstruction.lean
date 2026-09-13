import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Ring

/-!
# No additive injection `ℤ × ℤ → ℤ`

The terminal arithmetic of the counterexample to the first part of STW Problem XCV.  A
Cu-isomorphism `Cu(F) ≅ Cu(𝒵)` sends compact classes to compact classes, and the compact part of
`Cu(𝒵)` is `ℕ`.  For a stably finite `F`, the Murray--von Neumann semigroup `V(F)` embeds in the
compact part of `Cu(F)`, so `V(F)` embeds additively in `ℕ` and its Grothendieck group `K₀(F)`
embeds in `ℤ`.  For `F = E ⊗ E` with the witness `E` of the research node
`stw95-cu-z-tensor-counterexample`, `K₀(F) = ℤ²`, and this file supplies the final step: there is
no injective additive map `ℤ × ℤ → ℤ`.

This is stronger than `int_not_addEquiv_int_prod_int` in
`GroupApproximation/Manuscript/NinetyNineProblems/ProblemXCVCompactKTheory.lean`, which excludes
only additive isomorphisms.
-/

namespace GroupApproximation
namespace CuTensor

/-- An additive map `ℤ × ℤ → ℤ` is determined by its values on the two unit vectors. -/
theorem intProdInt_addMonoidHom_apply (f : ℤ × ℤ →+ ℤ) (m n : ℤ) :
    f (m, n) = m * f (1, 0) + n * f (0, 1) := by
  have h : ((m, n) : ℤ × ℤ) = m • ((1 : ℤ), (0 : ℤ)) + n • ((0 : ℤ), (1 : ℤ)) := by
    ext <;> simp
  simp only [h, map_add, map_zsmul, smul_eq_mul]

/-- **No additive injection `ℤ × ℤ → ℤ`.** The kernel contains `(f (0, 1), -f (1, 0))`, which
is nonzero unless both values vanish, and then `(1, 0)` lies in the kernel. -/
theorem not_injective_intProdInt_addMonoidHom (f : ℤ × ℤ →+ ℤ) : ¬ Function.Injective f := by
  intro hf
  have h0 : f (f (0, 1), -f (1, 0)) = 0 := by
    rw [intProdInt_addMonoidHom_apply f (f (0, 1)) (-f (1, 0))]
    ring
  have hker : ((f (0, 1), -f (1, 0)) : ℤ × ℤ) = 0 := hf (h0.trans (map_zero f).symm)
  have ha : f (1, 0) = 0 := by simpa using congrArg Prod.snd hker
  have h10 : ((1 : ℤ), (0 : ℤ)) = 0 := hf (ha.trans (map_zero f).symm)
  simpa using congrArg Prod.fst h10

/-- The form used downstream: no additive map from `ℤ × ℤ` to `ℤ` is injective, so no group
containing a copy of `ℤ × ℤ` embeds additively in `ℤ`. -/
theorem not_injective_of_intProdInt_embedding {G : Type*} [AddCommGroup G] (g : ℤ × ℤ →+ G)
    (hg : Function.Injective g) (f : G →+ ℤ) : ¬ Function.Injective f := fun hf =>
  not_injective_intProdInt_addMonoidHom (f.comp g) (hf.comp hg)

end CuTensor
end GroupApproximation
