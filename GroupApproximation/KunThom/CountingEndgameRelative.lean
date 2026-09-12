import GroupApproximation.KunThom.CountingEndgameSelection
import GroupApproximation.KunThom.CountingEndgameRestrict

/-!
# The counting endgame between restricted presentations

The relative cluster functor of a compressor
(`GroupoidPresentation.ClusterMetric.relativeFunctor`, Kun–Thom arXiv:2608.06222v3,
Lemma 4.3) runs from `(P.restrict R).Obj` to `(Q.restrict D).Obj`, with object
map `obj : R → D` (`relativeFunctor_obj`) and faithful under its numerical
hypotheses (`relativeFunctor_faithful`).  This file instantiates the finite
endgame `CountingEndgame.exists_bisection_lift_selected` for any faithful functor
of that shape.  The source is carried into `P.Obj` by the inclusion of
`P.restrict R`, and the target by the inclusion of `Q.restrict D`.  Nothing here
depends on the hypotheses under which the relative functor is built.

* `obj_injective_of_val`: a functor between restricted presentations whose
  object map is an injective `obj : R → D` is injective on objects.
* `exists_bisection_lift_restrict`: for a total bisection of `Q.Obj`, some total
  bisection of `P.Obj` carries, at every selected object, the inclusion of a
  preimage of the transported arrow.
-/

universe u v u' v'

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory GroupoidPresentation

/-- A functor between restricted presentations whose object map is an injective
map `obj : R → D` is injective on objects. -/
theorem obj_injective_of_val {I : Type u} {J : Type u'}
    {P : GroupoidPresentation.{u, v} I} {Q : GroupoidPresentation.{u', v'} J}
    {R : Set I} {D : Set J} (F : (P.restrict R).Obj ⥤ (Q.restrict D).Obj) (obj : R → D)
    (hobj : Function.Injective obj) (hF : ∀ X, (F.obj X).val = obj X.val) :
    Function.Injective F.obj := by
  intro X Y h
  obtain ⟨x⟩ := X
  obtain ⟨y⟩ := Y
  have h₁ : obj x = obj y := (hF ⟨x⟩).symm.trans ((congrArg Obj.val h).trans (hF ⟨y⟩))
  have h₂ : x = y := hobj h₁
  subst h₂
  rfl

/-- **The finite endgame between restricted presentations.**  Let
`F : (P.restrict R).Obj ⥤ (Q.restrict D).Obj` be faithful and injective on
objects, and write `K` for the inclusion of `Q.restrict D`.  For every total
bisection `a` of `Q.Obj` and every choice `sel` of targets, some total bisection
of `P.Obj` has, at every object `X` of `selected (F ⋙ K) a sel`, the inclusion of
a preimage `g : X ⟶ sel X` of the transported arrow of `a`. -/
theorem exists_bisection_lift_restrict {I : Type u} [Fintype I] [DecidableEq I]
    {J : Type u'} [Fintype J] [DecidableEq J]
    {P : GroupoidPresentation.{u, v} I} {Q : GroupoidPresentation.{u', v'} J}
    [∀ i j, Finite (P.Rep i j)] [∀ i j, Finite (Q.Rep i j)] {R : Set I} {D : Set J}
    [Fintype R] (F : (P.restrict R).Obj ⥤ (Q.restrict D).Obj) [F.Faithful]
    (hF : Function.Injective F.obj) (a : FiniteGroupoid.Bisection Q.Obj)
    (sel : (P.restrict R).Obj → (P.restrict R).Obj) :
    ∃ b : FiniteGroupoid.Bisection P.Obj,
      ∀ X (hX : X ∈ selected (F ⋙ Q.restrictInclusionFunctor D) a sel),
        ∃ g : X ⟶ sel X,
          (F ⋙ Q.restrictInclusionFunctor D).map g =
            a.hom ((F ⋙ Q.restrictInclusionFunctor D).obj X) ≫
              eqToHom ((mem_selected _ a sel X).mp hX).1.symm ∧
          ∃ e : b.objEquiv ((P.restrictInclusionFunctor R).obj X) =
              (P.restrictInclusionFunctor R).obj (sel X),
            b.hom ((P.restrictInclusionFunctor R).obj X) ≫ eqToHom e =
              (P.restrictInclusionFunctor R).map g :=
  exists_bisection_lift_selected (P.restrictInclusionFunctor R)
    (P.restrictInclusionFunctor_obj_injective R) (F ⋙ Q.restrictInclusionFunctor D)
    ((Q.restrictInclusionFunctor_obj_injective D).comp hF) a sel

end CountingEndgame
end GroupApproximation
