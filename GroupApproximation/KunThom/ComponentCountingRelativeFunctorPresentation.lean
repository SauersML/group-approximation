import GroupApproximation.Matching.FiniteGroupoidPresentation

/-!
# Functors between presented groupoids

Kun and Thom (arXiv:2608.06222, Lemma 4.3) define the relative cluster functor
on representatives.  An allowed partial bijection is transported through the
matching bridges of a compressor and then improved.  This file isolates the
algebraic descent of that construction.

* `GroupoidPresentation.restrict`: the presentation on a subset of the objects,
  with the same representatives and setoids.  Connectedness in the restriction
  is connectedness in the ambient presentation (`restrict_nonempty_hom_iff`).
* `GroupoidPresentation.Morphism`: a map of representatives that respects the
  setoids, and identities and composition up to the setoids.
* `Morphism.toFunctor`: the induced functor of presented groupoids.
* `Morphism.toFunctor_faithful`: the functor is faithful when the map of
  representatives reflects the setoids.
-/

namespace GroupApproximation
namespace GroupoidPresentation

open CategoryTheory

universe u u' v v'

variable {I : Type u} {J : Type u'}

/-- The presentation on a subset of the objects, with the same representatives
and setoids. -/
def restrict (P : GroupoidPresentation.{u, v} I) (R : Set I) :
    GroupoidPresentation.{u, v} R where
  Rep X Y := P.Rep X.1 Y.1
  rel X Y := P.rel X.1 Y.1
  one X := P.one X.1
  comp f g := P.comp f g
  inv f := P.inv f
  comp_respects hf hg := P.comp_respects hf hg
  inv_respects hf := P.inv_respects hf
  one_comp f := P.one_comp f
  comp_one f := P.comp_one f
  assoc f g h := P.assoc f g h
  inv_comp f := P.inv_comp f
  comp_inv f := P.comp_inv f

/-- An arrow of the restricted presentation is an arrow of the ambient
presentation between the same objects. -/
theorem restrict_nonempty_hom_iff (P : GroupoidPresentation.{u, v} I) (R : Set I)
    (X Y : (P.restrict R).Obj) :
    Nonempty (X ⟶ Y) ↔ Nonempty ((⟨X.val.1⟩ : P.Obj) ⟶ ⟨Y.val.1⟩) :=
  Iff.rfl

/-- A map of representatives that respects the setoids, and identities and
composition up to the setoids. -/
structure Morphism (P : GroupoidPresentation.{u, v} I)
    (Q : GroupoidPresentation.{u', v'} J) where
  /-- The object map. -/
  obj : I → J
  /-- The map of representatives. -/
  map : ∀ {X Y : I}, P.Rep X Y → Q.Rep (obj X) (obj Y)
  map_respects : ∀ {X Y : I} {f g : P.Rep X Y},
    P.rel X Y f g → Q.rel (obj X) (obj Y) (map f) (map g)
  map_one : ∀ X : I, Q.rel (obj X) (obj X) (map (P.one X)) (Q.one (obj X))
  map_comp : ∀ {X Y Z : I} (f : P.Rep X Y) (g : P.Rep Y Z),
    Q.rel (obj X) (obj Z) (map (P.comp f g)) (Q.comp (map f) (map g))

namespace Morphism

variable {P : GroupoidPresentation.{u, v} I} {Q : GroupoidPresentation.{u', v'} J}

/-- The functor of presented groupoids induced by a morphism of presentations. -/
def toFunctor (F : P.Morphism Q) : P.Obj ⥤ Q.Obj where
  obj X := ⟨F.obj X.val⟩
  map {X Y} f := Quotient.liftOn f
    (fun a ↦ @Quotient.mk _ (Q.rel (F.obj X.val) (F.obj Y.val)) (F.map a))
    (fun _ _ h ↦ @Quotient.sound _ (Q.rel (F.obj X.val) (F.obj Y.val)) _ _
      (F.map_respects h))
  map_id X := by
    show @Quotient.mk _ (Q.rel (F.obj X.val) (F.obj X.val)) (F.map (P.one X.val)) =
      @Quotient.mk _ (Q.rel (F.obj X.val) (F.obj X.val)) (Q.one (F.obj X.val))
    exact @Quotient.sound _ (Q.rel (F.obj X.val) (F.obj X.val)) _ _ (F.map_one X.val)
  map_comp {X Y Z} f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        exact @Quotient.sound _ (Q.rel (F.obj X.val) (F.obj Z.val)) _ _ (F.map_comp f g)

@[simp] theorem toFunctor_obj (F : P.Morphism Q) (X : P.Obj) :
    (F.toFunctor.obj X).val = F.obj X.val :=
  rfl

/-- On a representative, the induced functor is the map of representatives. -/
theorem toFunctor_map_ofRep (F : P.Morphism Q) {X Y : P.Obj} (f : P.Rep X.val Y.val) :
    F.toFunctor.map (P.ofRep f) = Q.ofRep (X := F.toFunctor.obj X) (Y := F.toFunctor.obj Y)
      (F.map f) :=
  rfl

/-- The induced functor is faithful when the map of representatives reflects the
setoids. -/
theorem toFunctor_faithful (F : P.Morphism Q)
    (hreflect : ∀ {X Y : I} {f g : P.Rep X Y},
      Q.rel (F.obj X) (F.obj Y) (F.map f) (F.map g) → P.rel X Y f g) :
    F.toFunctor.Faithful where
  map_injective {X Y} f g h := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        exact @Quotient.sound _ (P.rel X.val Y.val) _ _ (hreflect (Quotient.exact h))

end Morphism

end GroupoidPresentation
end GroupApproximation
