import GroupApproximation.CharClass.ThomBridgeNatural
import GroupApproximation.CharClass.RelativeFunctorial

/-!
# The hyperplane step is natural in the base

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

Second square of the naturality layer.  `ThomBridgeHyperplane`'s step is a
`relPullback` along the **identity** that shrinks the subspace from the
complement of the zero section to the hyperplane, so its naturality is the
statement that shrinking commutes with restricting the base.

It needs no geometry.  Both routes around the square are `relPullback` along the
same map, because the identity composes away on either side, and `relPullback`
does not depend on which proof witnesses the map-of-pairs condition.  So this is
one application of `relPullback_comp` in each direction and a transport across
`f ≫ 𝟙 = 𝟙 ≫ f`.

The four map-of-pairs conditions are arguments rather than assumptions, and at
the bridge they are discharged by `cc-bundle`'s landed lemmas: the hyperplane one
by `projInclOn_projIncl`, the complement one by
`projInclOn_mem_notZeroOpensSet_iff`, both definitional.

## Main declaration

* `relPullback_id_comm` — shrinking a subspace commutes with pulling back.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

variable {X Y : TopCat.{0}}

/-- **Shrinking the subspace commutes with pulling back.**  Both routes are
`relPullback` along `f`; the identity composes away on either side. -/
theorem relPullback_id_comm (f : Y ⟶ X) {A B : Set X} {A' B' : Set Y}
    (hAB : ∀ x ∈ A, (ConcreteCategory.hom (𝟙 X)) x ∈ B)
    (hA'B' : ∀ y ∈ A', (ConcreteCategory.hom (𝟙 Y)) y ∈ B')
    (hA : ∀ y ∈ A', (ConcreteCategory.hom f) y ∈ A)
    (hB : ∀ y ∈ B', (ConcreteCategory.hom f) y ∈ B)
    (hfid : ∀ y ∈ A', (ConcreteCategory.hom (f ≫ 𝟙 X)) y ∈ B)
    (hidf : ∀ y ∈ A', (ConcreteCategory.hom (𝟙 Y ≫ f)) y ∈ B)
    (n : ℕ) :
    relPullback (ZMod 2) (𝟙 X) hAB n ≫ relPullback (ZMod 2) f hA n
      = relPullback (ZMod 2) f hB n ≫ relPullback (ZMod 2) (𝟙 Y) hA'B' n := by
  have hL := relPullback_comp (ZMod 2) f (𝟙 X) hA hAB hfid n
  have hR := relPullback_comp (ZMod 2) (𝟙 Y) f hA'B' hB hidf n
  rw [← hL, ← hR]
  exact relPullback_eq_of_eq (ZMod 2)
    ((Category.comp_id f).trans (Category.id_comp f).symm) hfid n

/-! Printed on every build. -/

#print axioms relPullback_id_comm

end

end GroupApproximation.CharClass
