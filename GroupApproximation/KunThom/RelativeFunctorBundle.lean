import GroupApproximation.KunThom.RelativeFunctorAssembly

/-!
# The relative cluster functor as one bundle

Kun and Thom (arXiv:2608.06222, Lemma 4.3) state the relative cluster functor
with a matching `π_n : D_n → R_n` and the object condition `F_n (π_n i) = i`.
This file packages the assembly of `RelativeFunctorAssembly` in that form.

* `GroupoidPresentation.RelativeClusterFunctor P R D` bundles three things: a map
  `π` of objects that is a bijection from `D` onto `R`; a morphism of the
  presentations restricted to `R` and to `D` that sends `π i` to `i`; and the
  faithfulness of its functor.
* `ClusterMetric.matchingInverse`: the inverse of such a `π` on `R`, with
  `apply_matchingInverse` and `matchingInverse_apply`.
* `ClusterMetric.relativeClusterFunctor`: the bundle produced by
  `relativeMorphism` and `relativeFunctor_faithful`, with object map
  `matchingInverse π`.
-/

namespace GroupApproximation
namespace GroupoidPresentation

open FinitePartialBijection

universe u v

/-- **Kun–Thom, Lemma 4.3, as one bundle.**  It consists of a bijection `π` from
`D` onto `R`, a morphism of the presentations restricted to `R` and to `D` that
sends `π i` to `i`, and the faithfulness of its functor. -/
structure RelativeClusterFunctor {I : Type u} (P : GroupoidPresentation.{u, v} I)
    (R D : Finset I) where
  /-- The matching of objects, a bijection from `D` onto `R`. -/
  π : I → I
  mapsTo : Set.MapsTo π D R
  injOn : Set.InjOn π D
  surjOn : Set.SurjOn π D R
  /-- The relative functor on representatives. -/
  F : (P.restrict (R : Set I)).Morphism (P.restrict (D : Set I))
  obj_π : ∀ i (hi : i ∈ D), F.obj ⟨π i, mapsTo (Finset.mem_coe.mpr hi)⟩ =
    ⟨i, Finset.mem_coe.mpr hi⟩
  faithful : F.toFunctor.Faithful

namespace ClusterMetric

variable {I : Type u} {P : GroupoidPresentation.{u, v} I}

/-- The inverse of a matching `π` from `D` onto `R`, on the objects of `R`. -/
noncomputable def matchingInverse {R D : Finset I} (π : I → I) (hsurj : Set.SurjOn π D R)
    (X : (R : Set I)) : (D : Set I) :=
  ⟨Classical.choose ((Set.mem_image π D X.1).mp (hsurj X.2)),
    (Classical.choose_spec ((Set.mem_image π D X.1).mp (hsurj X.2))).1⟩

/-- `π` sends the inverse of a retained object back to it. -/
theorem apply_matchingInverse {R D : Finset I} (π : I → I) (hsurj : Set.SurjOn π D R)
    (X : (R : Set I)) : π (matchingInverse π hsurj X).1 = X.1 :=
  (Classical.choose_spec ((Set.mem_image π D X.1).mp (hsurj X.2))).2

/-- The inverse of `π i` is `i`. -/
theorem matchingInverse_apply {R D : Finset I} (π : I → I) (hmaps : Set.MapsTo π D R)
    (hinj : Set.InjOn π D) (hsurj : Set.SurjOn π D R) {i : I} (hi : i ∈ D) :
    matchingInverse π hsurj ⟨π i, hmaps (Finset.mem_coe.mpr hi)⟩ =
      ⟨i, Finset.mem_coe.mpr hi⟩ :=
  Subtype.ext (hinj (matchingInverse π hsurj ⟨π i, hmaps (Finset.mem_coe.mpr hi)⟩).2
    (Finset.mem_coe.mpr hi)
    (apply_matchingInverse π hsurj ⟨π i, hmaps (Finset.mem_coe.mpr hi)⟩))

/-- **The relative cluster functor, bundled.**  The assembled morphism with object
map `matchingInverse π`, together with its faithfulness. -/
noncomputable def relativeClusterFunctor (MP : P.ClusterMetric) {R D : Finset I} (π : I → I)
    (hmaps : Set.MapsTo π D R) (hinj : Set.InjOn π D) (hsurj : Set.SurjOn π D R)
    (bridge : ∀ X : (R : Set I),
      FinitePartialBijection (MP.model X.1) (MP.model (matchingInverse π hsurj X).1))
    (β : ↥(R : Set I) → ℕ) (ρ : ↥(R : Set I) → ↥(R : Set I) → ℕ)
    (hbridge : ∀ X : (R : Set I), (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (himprove : ∀ (X Y : (R : Set I)) (b : P.Rep X.1 Y.1),
      ∃ r : P.Rep (matchingInverse π hsurj X).1 (matchingInverse π hsurj Y).1,
        (MP.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    (hrespects : ∀ {X Y : (R : Set I)}, P.Rep X.1 Y.1 →
      2 * ρ X Y + β X + β Y + MP.radius X.1 Y.1 ≤
        8 * MP.radius (matchingInverse π hsurj X).1 (matchingInverse π hsurj Y).1)
    (hcomp : ∀ {X Y Z : (R : Set I)}, P.Rep X.1 Y.1 → P.Rep Y.1 Z.1 →
      ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + MP.radius X.1 Z.1 +
        MP.radius X.1 Y.1 + MP.radius Y.1 Z.1 +
          MP.radius (matchingInverse π hsurj X).1 (matchingInverse π hsurj Z).1 ≤
            8 * MP.radius (matchingInverse π hsurj X).1 (matchingInverse π hsurj Z).1)
    (hfaithful : ∀ {X Y : (R : Set I)}, P.Rep X.1 Y.1 →
      2 * ρ X Y + 5 * β X + 5 * β Y + 2 * MP.radius X.1 Y.1 +
        MP.radius (matchingInverse π hsurj X).1 (matchingInverse π hsurj Y).1 ≤
          8 * MP.radius X.1 Y.1) :
    P.RelativeClusterFunctor R D where
  π := π
  mapsTo := hmaps
  injOn := hinj
  surjOn := hsurj
  F := relativeMorphism MP MP (matchingInverse π hsurj) bridge β ρ hbridge himprove
    hrespects hcomp
  obj_π _ hi := matchingInverse_apply π hmaps hinj hsurj hi
  faithful := relativeFunctor_faithful MP MP (matchingInverse π hsurj) bridge β ρ hbridge
    himprove hrespects hcomp hfaithful

end ClusterMetric

end GroupoidPresentation
end GroupApproximation
