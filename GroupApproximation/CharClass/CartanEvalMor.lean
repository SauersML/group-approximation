import GroupApproximation.CharClass.CartanEvalBoundary

/-!
# The evaluating functional as a map of group-ring modules

`DiagonalComparison.eval_sub_eq` wants the functional as a morphism of
`Λ`-modules out of the fourfold, annihilating boundaries, into a module on which
the generator acts trivially.  This file supplies all three.

The coefficient module is `ZMod 2` with the trivial action, packaged as a named
object so that nothing downstream has to carry the instance itself.  Linearity
over the group ring is the block-swap invariance of the functional, which is why
the action on the fourfold has to be `(13)(24)` and not `(12)(34)`.

## Main results

* `trivialCoeffMod` — the coefficient object.
* `fourEvalMor` — the functional `α ⊗ β ⊗ α ⊗ β` as a morphism.
* `fourEvalMor_comp_d` — it annihilates boundaries, when `α` and `β` are
  cocycles.
* `fourEvalMor_gen_smul` — the generator acts trivially on the target.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **The coefficient object**: `ZMod 2` over the mod-2 group ring of `ℤ/2`, with
the generator acting as the identity. -/
noncomputable def trivialCoeffMod : ModuleCat.{0} GroupRingZ2 :=
  letI := trivialCoeff
  ModuleCat.of GroupRingZ2 (ZMod 2)

theorem trivialCoeffMod_gen_smul (r : trivialCoeffMod) :
    (groupRingGen : GroupRingZ2) • r = r :=
  trivialCoeff_gen_smul r

/-- **The functional `α ⊗ β ⊗ α ⊗ β`**, as a morphism of group-ring modules out
of the fourfold.  Linearity is the block-swap invariance. -/
noncomputable def fourEvalMor (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) : (four.obj X).X k ⟶ trivialCoeffMod :=
  letI := trivialCoeff
  ModuleCat.ofHom
    ({ toFun := fourEvalF2 X p q α β k
       map_add' := fun u v => map_add _ u v
       map_smul' := fun c y => fourEval_galAlgHom X p q α β k c y } :
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) →ₗ[GroupRingZ2] ZMod 2)

@[simp] theorem fourEvalMor_hom (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) (y : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :
    (fourEvalMor X p q α β k).hom y = fourEvalF2 X p q α β k y := rfl

/-- **The functional annihilates boundaries**, when the two cochains are
cocycles. -/
theorem fourEvalMor_comp_d (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0) (k : ℕ) :
    (four.obj X).d (k + 2) (k + 1) ≫ fourEvalMor X p q α β (k + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have hd : ((fourCx X).d (k + 2) (k + 1)).hom y
      = tensorD (pairFreeCx X) (pairFreeCx X) (k + 1) y := by
    rw [fourCx_d]
    rfl
  show fourEvalF2 X p q α β (k + 1) (((fourCx X).d (k + 2) (k + 1)).hom y) = 0
  rw [hd]
  exact fourEvalF2_tensorD hα hβ (k + 1) y

end

end GroupApproximation.CharClass
