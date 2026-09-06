import GroupApproximation.CharClass.SteenrodFourfoldB

/-!
# The two composites agree in degree zero

The acyclic-models comparison needs exactly one equation relating the two
composites: that they agree in degree `0`.  Everything else about them is
separate.

Both send `e₀ ⊗ x` to `x ⊗ x ⊗ x ⊗ x`, which is `fourDiagZero`, so the equation
is `compA_zero` and `compB_zero` read against each other.  In degree `0` the
source is free on a single-index family — `Fin 1` is a subsingleton — so
comparing the two maps is comparing their values on `e₀ ⊗ x`, and nothing about
the chain-map property or naturality is involved.

This is `cc-cartan`'s `hzero` hypothesis, in the degreewise form; once `B` is
packaged as a natural transformation it is that hypothesis verbatim.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **The two composites agree in degree zero.**  Both take the value
`x ⊗ x ⊗ x ⊗ x` on the only kind of basis element there is. -/
theorem compA_eq_compB_zero (X : TopCat.{0}) : compA X 0 = compB X 0 := by
  apply Finsupp.lhom_ext'
  intro b
  apply LinearMap.ext_ring
  obtain ⟨n, φ⟩ := b
  revert φ
  induction n using Fin.cases with
  | succ i => exact i.elim0
  | zero =>
      intro φ
      show compA X 0 (Finsupp.single
          (⟨0, φ⟩ : Σ m : Fin (0 + 1), stdSimplexTop m.val ⟶ X) (1 : GroupRingZ2))
        = compB X 0 (Finsupp.single
          (⟨0, φ⟩ : Σ m : Fin (0 + 1), stdSimplexTop m.val ⟶ X) (1 : GroupRingZ2))
      rw [compA_zero, compB_zero]

end

end Steenrod
end CharClass
end GroupApproximation
