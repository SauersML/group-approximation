import GroupApproximation.CharClass.CartanComposeA
import GroupApproximation.CharClass.CartanEvaluation

/-!
# The acyclic-models comparison of the two composites

Three of the four hypotheses of the comparison are proved: the source is free on
the models, the fourfold is acyclic on them, and the first composite is a natural
transformation into it.  The fourth, `cc-steenrod`'s second composite, is taken
here as a **named hypothesis**, so that the assembly is finished now and closes
by substitution the moment their chain map and naturality land.

Two hypotheses only: `compB`, a natural transformation `W ⊗ S(X) ⟶ S(X)^{⊗4}`,
and the single equation saying it agrees with the first composite in degree zero.
Both composites take the value `x ⊗ x ⊗ x ⊗ x` on `e₀ ⊗ x`, so the equation is
available on `cc-steenrod`'s side directly.

## Main results

* `pairFreeCx_d`, `fourFreeCx_d` — the differentials of the pair and the
  fourfold, without forcing the structure projection.
* `cartanComparison` — **the comparison data.**
* `cartanHomotopy` — the natural equivariant chain homotopy between the two
  composites.
* `cartan_eval` — **the evaluated comparison**, in the shape the last step
  consumes: a functional killing boundaries sees the two composites differ by an
  explicit coboundary, and the `(1 + t)` half of the source differential
  contributes nothing.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. The differentials, without the projection -/

/-- The differential of the pair complex.  Stated so that nothing downstream has
to force the structure projection of `tensorFreeCx`, whose `d_d` field is a large
proof and makes `whnf` expensive. -/
theorem pairFreeCx_d (X : TopCat.{0}) (k : ℕ) :
    (pairFreeCx X).d k = tensorD (singFreeCx X) (singFreeCx X) k := rfl

/-- The differential of the fourfold complex. -/
theorem fourFreeCx_d (X : TopCat.{0}) (k : ℕ) :
    (fourFreeCx X).d k = tensorD (pairFreeCx X) (pairFreeCx X) k := rfl

/-! ## 2. The comparison data -/

variable (compB : src singularBoundary ⟶ four)
variable (hzero : ∀ X : TopCat.{0}, (compA.app X).f 0 = (compB.app X).f 0)

/-- **The comparison data of the Cartan formula.**  The source is free on the
standard simplices, the fourfold is acyclic on them, and the two composites are
natural transformations agreeing in degree zero. -/
noncomputable def cartanComparison :
    DiagonalComparison stdSimplexTop GroupRingZ2 (src singularBoundary) four where
  free := srcFree singularBoundary
  acyclic := four_acyclicOnModels
  Φ₁ := compA
  Φ₂ := compB
  agree_zero := hzero

@[simp] theorem cartanComparison_Φ₁ : (cartanComparison compB hzero).Φ₁ = compA := rfl

@[simp] theorem cartanComparison_Φ₂ : (cartanComparison compB hzero).Φ₂ = compB := rfl

/-- **The natural equivariant chain homotopy** between the two composites. -/
noncomputable def cartanHomotopy :
    NaturalHomotopy (src singularBoundary) four compA compB :=
  (cartanComparison compB hzero).homotopy

/-! ## 3. The evaluated comparison -/

/-- **The comparison, evaluated.**  A functional on the fourfold that kills
boundaries and on which the group ring acts trivially sees the two composites
differ by an explicit coboundary; the `(1 + t)` half of the source differential
contributes nothing, because a `Λ`-linear functional into a trivial-action module
kills it in characteristic two. -/
theorem cartan_eval (X : TopCat.{0}) (n : ℕ)
    {R : ModuleCat.{0} GroupRingZ2} (u : (four.obj X).X (n + 1) ⟶ R)
    (hu : (four.obj X).d (n + 2) (n + 1) ≫ u = 0)
    (htriv : ∀ r : R, (groupRingGen : GroupRingZ2) • r = r)
    (x : ((src singularBoundary).obj X).X (n + 1))
    (y z : ((src singularBoundary).obj X).X n)
    (hx : (((src singularBoundary).obj X).d (n + 1) n).hom x
      = (1 + groupRingGen) • y + z) :
    ((compA.app X).f (n + 1) ≫ u).hom x
      = ((compB.app X).f (n + 1) ≫ u).hom x
        + ((cartanHomotopy compB hzero).s n X ≫ u).hom z :=
  (cartanComparison compB hzero).eval_sub_eq X n u hu groupRingGen htriv
    two_eq_zero_groupRingZ2 x y z hx

include hzero in
/-- In degree zero the two evaluations agree on the nose. -/
theorem cartan_eval_zero (X : TopCat.{0})
    {R : ModuleCat.{0} GroupRingZ2} (u : (four.obj X).X 0 ⟶ R)
    (hu : (four.obj X).d 1 0 ≫ u = 0) :
    (compA.app X).f 0 ≫ u = (compB.app X).f 0 ≫ u :=
  (cartanComparison compB hzero).cochain_zero X u hu

end

end GroupApproximation.CharClass
