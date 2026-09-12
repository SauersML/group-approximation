import GroupApproximation.KunThom.RelativeFunctorBundle
import GroupApproximation.KunThom.CountingEndgameRelative

/-!
# The counting endgame for the bundled relative cluster functor

`GroupoidPresentation.RelativeClusterFunctor P R D` bundles Kun and Thom's
relative cluster functor (arXiv:2608.06222v3, Lemma 4.3): a matching `π` from `D`
onto `R`, a morphism of the restricted presentations sending `π i` to `i`, and
its faithfulness.  This file applies the finite counting endgame
`CountingEndgame.exists_bisection_lift_restrict` to the bundle, with source and
target in the one cluster groupoid `P`.

* `RelativeClusterFunctor.obj_injective`, `toFunctor_obj_injective`: every
  retained object is some `π i`, and it goes to `i`, so the functor is injective
  on objects.
* `RelativeClusterFunctor.exists_bisection_lift`: for a total bisection of
  `P.Obj`, some total bisection of `P.Obj` carries, at every selected retained
  object, the inclusion of a preimage of the transported arrow.
-/

universe u v

namespace GroupApproximation
namespace GroupoidPresentation
namespace RelativeClusterFunctor

open CategoryTheory CountingEndgame

variable {I : Type u} {P : GroupoidPresentation.{u, v} I} {R D : Finset I}

/-- The object map of a bundled relative cluster functor is injective. -/
theorem obj_injective (𝓕 : P.RelativeClusterFunctor R D) : Function.Injective 𝓕.F.obj := by
  intro X Y h
  obtain ⟨i, hi, hiX⟩ := 𝓕.surjOn X.2
  obtain ⟨j, hj, hjY⟩ := 𝓕.surjOn Y.2
  have hX : X = ⟨𝓕.π i, 𝓕.mapsTo hi⟩ := Subtype.ext hiX.symm
  have hY : Y = ⟨𝓕.π j, 𝓕.mapsTo hj⟩ := Subtype.ext hjY.symm
  subst hX
  subst hY
  have h₁ := 𝓕.obj_π i (Finset.mem_coe.mp hi)
  have h₂ := 𝓕.obj_π j (Finset.mem_coe.mp hj)
  rw [h₁, h₂] at h
  have hij : i = j := congrArg Subtype.val h
  subst hij
  rfl

/-- The functor of a bundled relative cluster functor is injective on objects. -/
theorem toFunctor_obj_injective (𝓕 : P.RelativeClusterFunctor R D) :
    Function.Injective 𝓕.F.toFunctor.obj :=
  obj_injective_of_val 𝓕.F.toFunctor 𝓕.F.obj 𝓕.obj_injective fun _ ↦ rfl

/-- **The finite counting endgame for a bundled relative cluster functor.**  Write
`F` for its functor and `K` for the inclusion of `P.restrict D`.  For every total
bisection `a` of `P.Obj` and every choice `sel` of targets, some total bisection of
`P.Obj` has, at every object `X` of `selected (F ⋙ K) a sel`, the inclusion of a
preimage `g : X ⟶ sel X` of the transported arrow of `a`. -/
theorem exists_bisection_lift [Fintype I] [DecidableEq I] [∀ i j, Finite (P.Rep i j)]
    (𝓕 : P.RelativeClusterFunctor R D) (a : FiniteGroupoid.Bisection P.Obj)
    (sel : (P.restrict (R : Set I)).Obj → (P.restrict (R : Set I)).Obj) :
    ∃ b : FiniteGroupoid.Bisection P.Obj,
      ∀ X (hX : X ∈ selected (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (D : Set I)) a sel),
        ∃ g : X ⟶ sel X,
          (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (D : Set I)).map g =
            a.hom ((𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (D : Set I)).obj X) ≫
              eqToHom ((mem_selected _ a sel X).mp hX).1.symm ∧
          ∃ e : b.objEquiv ((P.restrictInclusionFunctor (R : Set I)).obj X) =
              (P.restrictInclusionFunctor (R : Set I)).obj (sel X),
            b.hom ((P.restrictInclusionFunctor (R : Set I)).obj X) ≫ eqToHom e =
              (P.restrictInclusionFunctor (R : Set I)).map g := by
  haveI := 𝓕.faithful
  exact exists_bisection_lift_restrict 𝓕.F.toFunctor 𝓕.toFunctor_obj_injective a sel

end RelativeClusterFunctor
end GroupoidPresentation
end GroupApproximation
