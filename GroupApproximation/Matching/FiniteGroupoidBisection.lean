import GroupApproximation.Matching.FiniteGroupoidCounting

/-!
# Bisections of finite groupoids

A bisection is a permutation of the objects together with one arrow from
each object to its image.  A full finite-groupoid endofunctor transports
bisections back across its object permutation.  This is the categorical
normalization step used after the finite counting argument proves fullness.
-/

namespace GroupApproximation
namespace FiniteGroupoid

open CategoryTheory

universe u v

variable {C : Type u} [Groupoid.{v} C]

/-- A groupoid bisection: a permutation of objects and an arrow realizing it
at every object. -/
structure Bisection (C : Type u) [Groupoid.{v} C] where
  objEquiv : C ≃ C
  hom : ∀ X, X ⟶ objEquiv X

/-- An injective self-map of a finite type, bundled as a permutation. -/
noncomputable def objectEquivOfInjective [Fintype C]
    (F : C ⥤ C) (hobj : Function.Injective F.obj) : C ≃ C :=
  Equiv.ofBijective F.obj
    ((Fintype.bijective_iff_injective_and_card F.obj).2 ⟨hobj, rfl⟩)

@[simp] theorem objectEquivOfInjective_apply [Fintype C]
    (F : C ⥤ C) (hobj : Function.Injective F.obj) (X : C) :
    objectEquivOfInjective F hobj X = F.obj X := rfl

/-- Pull a bisection back through a full endofunctor which is injective on
objects.  The new object permutation is `F⁻¹ β F`; fullness supplies each
required arrow. -/
noncomputable def pullbackBisection [Fintype C]
    (F : C ⥤ C) [F.Full] (hobj : Function.Injective F.obj)
    (β : Bisection C) : Bisection C where
  objEquiv :=
    (objectEquivOfInjective F hobj).trans
      (β.objEquiv.trans (objectEquivOfInjective F hobj).symm)
  hom X := by
    let e := objectEquivOfInjective F hobj
    let Y := e.symm (β.objEquiv (F.obj X))
    have htarget : F.obj Y = β.objEquiv (F.obj X) := by
      change e Y = β.objEquiv (F.obj X)
      exact e.apply_symm_apply _
    exact F.preimage (β.hom (F.obj X) ≫ eqToHom htarget.symm)

/-- The transported arrow maps to the original bisection arrow, followed
only by the definitional target identification. -/
theorem map_pullbackBisection_hom [Fintype C]
    (F : C ⥤ C) [F.Full] (hobj : Function.Injective F.obj)
    (β : Bisection C) (X : C) :
    F.map ((pullbackBisection F hobj β).hom X) =
      β.hom (F.obj X) ≫ eqToHom (by
        let e := objectEquivOfInjective F hobj
        let Y := e.symm (β.objEquiv (F.obj X))
        change β.objEquiv (F.obj X) = F.obj Y
        exact (e.apply_symm_apply _).symm) := by
  exact F.map_preimage _

/-- The complete finite counting step: cardinal preservation first upgrades
a faithful object-injective endofunctor to a full functor, after which every
bisection pulls back.  No fullness hypothesis remains in the interface. -/
noncomputable def pullbackBisectionOfCardinalPreserving [Fintype C]
    [∀ X Y : C, Fintype (X ⟶ Y)]
    (F : C ⥤ C) [F.Faithful]
    (hobj : Function.Injective F.obj)
    (horbit : ∀ X, (orbit X).card = (orbit (F.obj X)).card)
    (hvertex : ∀ X,
      Fintype.card (X ⟶ X) = Fintype.card (F.obj X ⟶ F.obj X))
    (β : Bisection C) : Bisection C := by
  letI : F.Full :=
    fullOfFaithfulOfCardinalPreserving F hobj horbit hvertex
  exact pullbackBisection F hobj β

end FiniteGroupoid
end GroupApproximation
