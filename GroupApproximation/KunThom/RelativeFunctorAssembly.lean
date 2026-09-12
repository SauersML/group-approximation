import GroupApproximation.KunThom.RelativeFunctorMetric

/-!
# The relative cluster functor of a compressor

For a compressor `t`, Kun and Thom (arXiv:2608.06222, Lemma 4.3) build a faithful
functor.  Its source is the cluster groupoid restricted to the retained objects
`R`, and its target is the cluster groupoid restricted to their matched objects
`D`.  A representative `b` between retained objects `X` and `Y` is transported
through the bridges at `X` and `Y` (`FinitePartialBijection.sandwich`).  The
functor sends it to the class of an improvement of the transported map.

This file assembles that functor from explicit finite hypotheses, for any two
presentations with a `ClusterMetric`.  Radii are attached to pairs of objects,
as in `ScaledFinitePartialClusterData`.

* `transportRep`: the chosen improvement of a transported representative, with
  `transportRep_close`.
* `relativeMorphism` and `relativeFunctor`: the morphism of the restricted
  presentations and its functor.  The object map is `obj`, recorded by
  `relativeFunctor_obj`.  With `obj = π.symm` for a matching `π : D ≃ R`, this
  is `F (π i) = i`.
* `relativeFunctor_faithful`: faithfulness.
* `twoSidedDisagreement_sandwich_lt_of_ofRep_eq`: estimate (7).  Every
  representative of the image class lies within the target radius plus the
  improvement radius of the transported map.
* `nonempty_hom_relativeFunctor`: connected retained objects have connected
  images in the target groupoid.

The hypotheses are:
- `himprove`: every transported representative has an improvement within `ρ`;
- `hbridge`: `β` bounds the missing mass of every bridge;
- `hrespects`, `hcomp` and `hfaithful`: three families of numerical
  inequalities, each required only between objects joined by a representative.
For `ScaledPartialClusterSystem`, `ScaledPartialClusterSystem.repair_spec`
produces `himprove` once the transported map has small equivariance defects.
-/

namespace GroupApproximation
namespace GroupoidPresentation
namespace ClusterMetric

open CategoryTheory FinitePartialBijection

universe u u' v v'

variable {I : Type u} {J : Type u'}
variable {P : GroupoidPresentation.{u, v} I} {Q : GroupoidPresentation.{u', v'} J}
variable (MP : P.ClusterMetric) (MQ : Q.ClusterMetric)
variable {R : Set I} {D : Set J} (obj : R → D)
variable (bridge : ∀ X : R, FinitePartialBijection (MP.model X.1) (MQ.model (obj X).1))
variable (β : R → ℕ) (ρ : R → R → ℕ)

/-- The chosen improvement of the transport of a representative through the
bridges at its source and target. -/
noncomputable def transportRep
    (himprove : ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : Q.Rep (obj X).1 (obj Y).1,
      (MQ.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    {X Y : R} (b : P.Rep X.1 Y.1) : Q.Rep (obj X).1 (obj Y).1 :=
  Classical.choose (himprove X Y b)

/-- The chosen improvement is within `ρ` of the transported representative. -/
theorem transportRep_close
    (himprove : ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : Q.Rep (obj X).1 (obj Y).1,
      (MQ.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    {X Y : R} (b : P.Rep X.1 Y.1) :
    (MQ.val (transportRep MP MQ obj bridge ρ himprove b)).twoSidedDisagreement
      (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y :=
  Classical.choose_spec (himprove X Y b)

/-- **The relative cluster functor on representatives.**  The object map is
`obj`, and a representative goes to the chosen improvement of its transport. -/
noncomputable def relativeMorphism
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (himprove : ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : Q.Rep (obj X).1 (obj Y).1,
      (MQ.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    (hrespects : ∀ {X Y : R}, P.Rep X.1 Y.1 →
      2 * ρ X Y + β X + β Y + MP.radius X.1 Y.1 ≤ 8 * MQ.radius (obj X).1 (obj Y).1)
    (hcomp : ∀ {X Y Z : R}, P.Rep X.1 Y.1 → P.Rep Y.1 Z.1 →
      ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + MP.radius X.1 Z.1 +
        MP.radius X.1 Y.1 + MP.radius Y.1 Z.1 + MQ.radius (obj X).1 (obj Z).1 ≤
          8 * MQ.radius (obj X).1 (obj Z).1) :
    (P.restrict R).Morphism (Q.restrict D) where
  obj := obj
  map {X Y} b := transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) b
  map_respects {X Y} {f g} hfg := by
    show Q.rel (obj X).1 (obj Y).1
      (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) f)
      (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) g)
    refine MQ.rel_of_lt ?_
    have hd := MP.lt_of_rel (X := X.1) (Y := Y.1) (f := f) (g := g) hfg
    have hchain := twoSidedDisagreement_transport_le (bridge X) (bridge Y)
      (MP.val (X := X.1) (Y := Y.1) f) (MP.val (X := X.1) (Y := Y.1) g)
      (MQ.val (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) f))
      (MQ.val (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) g))
    have hf := transportRep_close MP MQ obj bridge ρ himprove (X := X) (Y := Y) f
    have hg := transportRep_close MP MQ obj bridge ρ himprove (X := X) (Y := Y) g
    have hX := hbridge X
    have hY := hbridge Y
    have hnum := hrespects (X := X) (Y := Y) f
    omega
  map_one X := by
    show Q.rel (obj X).1 (obj X).1
      (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := X) (P.one X.1))
      (Q.one (obj X).1)
    refine MQ.rel_of_lt ?_
    rw [MQ.val_one]
    have hclose := transportRep_close MP MQ obj bridge ρ himprove (X := X) (Y := X)
      (P.one X.1)
    rw [MP.val_one] at hclose
    have hchain := twoSidedDisagreement_transport_refl_le (bridge X)
      (MQ.val (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := X) (P.one X.1)))
    have hX := hbridge X
    have hnum := hrespects (X := X) (Y := X) (P.one X.1)
    omega
  map_comp {X Y Z} f g := by
    show Q.rel (obj X).1 (obj Z).1
      (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Z)
        (P.comp (X := X.1) (Y := Y.1) (Z := Z.1) f g))
      (Q.comp (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) f)
        (transportRep MP MQ obj bridge ρ himprove (X := Y) (Y := Z) g))
    refine MQ.rel_of_lt ?_
    have hchain := twoSidedDisagreement_transport_comp_le (bridge X) (bridge Y) (bridge Z)
      (MP.val (X := X.1) (Y := Y.1) f) (MP.val (X := Y.1) (Y := Z.1) g)
      (MP.val (P.comp (X := X.1) (Y := Y.1) (Z := Z.1) f g))
      (MQ.val (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Z)
        (P.comp (X := X.1) (Y := Y.1) (Z := Z.1) f g)))
      (MQ.val (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) f))
      (MQ.val (transportRep MP MQ obj bridge ρ himprove (X := Y) (Y := Z) g))
      (MQ.val (Q.comp (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) f)
        (transportRep MP MQ obj bridge ρ himprove (X := Y) (Y := Z) g)))
    have h₁ := transportRep_close MP MQ obj bridge ρ himprove (X := X) (Y := Z)
      (P.comp (X := X.1) (Y := Y.1) (Z := Z.1) f g)
    have h₂ := MP.comp_close (X := X.1) (Y := Y.1) (Z := Z.1) f g
    have h₃ := MP.self_small (X := X.1) (Y := Y.1) f
    have h₄ := MP.self_small (X := Y.1) (Y := Z.1) g
    have h₅ := transportRep_close MP MQ obj bridge ρ himprove (X := X) (Y := Y) f
    have h₆ := transportRep_close MP MQ obj bridge ρ himprove (X := Y) (Y := Z) g
    have h₇ := MQ.comp_close
      (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) f)
      (transportRep MP MQ obj bridge ρ himprove (X := Y) (Y := Z) g)
    have hX := hbridge X
    have hY := hbridge Y
    have hZ := hbridge Z
    have hnum := hcomp (X := X) (Y := Y) (Z := Z) f g
    omega

/-- **The relative cluster functor** (Kun–Thom, Lemma 4.3). -/
noncomputable def relativeFunctor
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (himprove : ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : Q.Rep (obj X).1 (obj Y).1,
      (MQ.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    (hrespects : ∀ {X Y : R}, P.Rep X.1 Y.1 →
      2 * ρ X Y + β X + β Y + MP.radius X.1 Y.1 ≤ 8 * MQ.radius (obj X).1 (obj Y).1)
    (hcomp : ∀ {X Y Z : R}, P.Rep X.1 Y.1 → P.Rep Y.1 Z.1 →
      ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + MP.radius X.1 Z.1 +
        MP.radius X.1 Y.1 + MP.radius Y.1 Z.1 + MQ.radius (obj X).1 (obj Z).1 ≤
          8 * MQ.radius (obj X).1 (obj Z).1) :
    (P.restrict R).Obj ⥤ (Q.restrict D).Obj :=
  (relativeMorphism MP MQ obj bridge β ρ hbridge himprove hrespects hcomp).toFunctor

/-- The relative functor sends a retained object `X` to `obj X`. -/
@[simp] theorem relativeFunctor_obj
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (himprove : ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : Q.Rep (obj X).1 (obj Y).1,
      (MQ.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    (hrespects : ∀ {X Y : R}, P.Rep X.1 Y.1 →
      2 * ρ X Y + β X + β Y + MP.radius X.1 Y.1 ≤ 8 * MQ.radius (obj X).1 (obj Y).1)
    (hcomp : ∀ {X Y Z : R}, P.Rep X.1 Y.1 → P.Rep Y.1 Z.1 →
      ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + MP.radius X.1 Z.1 +
        MP.radius X.1 Y.1 + MP.radius Y.1 Z.1 + MQ.radius (obj X).1 (obj Z).1 ≤
          8 * MQ.radius (obj X).1 (obj Z).1)
    (X : (P.restrict R).Obj) :
    ((relativeFunctor MP MQ obj bridge β ρ hbridge himprove hrespects hcomp).obj X).val =
      obj X.val :=
  rfl

/-- On a representative, the relative functor is the chosen improvement of its
transport. -/
theorem relativeFunctor_map_ofRep
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (himprove : ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : Q.Rep (obj X).1 (obj Y).1,
      (MQ.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    (hrespects : ∀ {X Y : R}, P.Rep X.1 Y.1 →
      2 * ρ X Y + β X + β Y + MP.radius X.1 Y.1 ≤ 8 * MQ.radius (obj X).1 (obj Y).1)
    (hcomp : ∀ {X Y Z : R}, P.Rep X.1 Y.1 → P.Rep Y.1 Z.1 →
      ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + MP.radius X.1 Z.1 +
        MP.radius X.1 Y.1 + MP.radius Y.1 Z.1 + MQ.radius (obj X).1 (obj Z).1 ≤
          8 * MQ.radius (obj X).1 (obj Z).1)
    {X Y : R} (b : P.Rep X.1 Y.1) :
    (relativeFunctor MP MQ obj bridge β ρ hbridge himprove hrespects hcomp).map
        ((P.restrict R).ofRep (X := ⟨X⟩) (Y := ⟨Y⟩) b) =
      (Q.restrict D).ofRep (X := ⟨obj X⟩) (Y := ⟨obj Y⟩)
        (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) b) :=
  rfl

/-- **Faithfulness** of the relative cluster functor. -/
theorem relativeFunctor_faithful
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (himprove : ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : Q.Rep (obj X).1 (obj Y).1,
      (MQ.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    (hrespects : ∀ {X Y : R}, P.Rep X.1 Y.1 →
      2 * ρ X Y + β X + β Y + MP.radius X.1 Y.1 ≤ 8 * MQ.radius (obj X).1 (obj Y).1)
    (hcomp : ∀ {X Y Z : R}, P.Rep X.1 Y.1 → P.Rep Y.1 Z.1 →
      ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + MP.radius X.1 Z.1 +
        MP.radius X.1 Y.1 + MP.radius Y.1 Z.1 + MQ.radius (obj X).1 (obj Z).1 ≤
          8 * MQ.radius (obj X).1 (obj Z).1)
    (hfaithful : ∀ {X Y : R}, P.Rep X.1 Y.1 →
      2 * ρ X Y + 5 * β X + 5 * β Y + 2 * MP.radius X.1 Y.1 + MQ.radius (obj X).1 (obj Y).1 ≤
        8 * MP.radius X.1 Y.1) :
    (relativeFunctor MP MQ obj bridge β ρ hbridge himprove hrespects hcomp).Faithful := by
  refine Morphism.toFunctor_faithful
    (relativeMorphism MP MQ obj bridge β ρ hbridge himprove hrespects hcomp) ?_
  intro X Y f g hfg
  show P.rel X.1 Y.1 f g
  refine MP.rel_of_lt ?_
  have hd := MQ.lt_of_rel (X := (obj X).1) (Y := (obj Y).1)
    (f := transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) f)
    (g := transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) g) hfg
  have hchain := twoSidedDisagreement_transport_reflect_le (bridge X) (bridge Y)
    (MP.val (X := X.1) (Y := Y.1) f) (MP.val (X := X.1) (Y := Y.1) g)
    (MQ.val (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) f))
    (MQ.val (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) g))
  have hf := transportRep_close MP MQ obj bridge ρ himprove (X := X) (Y := Y) f
  have hg := transportRep_close MP MQ obj bridge ρ himprove (X := X) (Y := Y) g
  have hsf := MP.self_small (X := X.1) (Y := Y.1) f
  have hsg := MP.self_small (X := X.1) (Y := Y.1) g
  have hX := hbridge X
  have hY := hbridge Y
  have hnum := hfaithful (X := X) (Y := Y) f
  omega

/-- **Estimate (7).**  Every representative `θ` of the image of the class of `b`
lies within the target radius plus the improvement radius of the transport of
`b`. -/
theorem twoSidedDisagreement_sandwich_lt_of_ofRep_eq
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (himprove : ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : Q.Rep (obj X).1 (obj Y).1,
      (MQ.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    (hrespects : ∀ {X Y : R}, P.Rep X.1 Y.1 →
      2 * ρ X Y + β X + β Y + MP.radius X.1 Y.1 ≤ 8 * MQ.radius (obj X).1 (obj Y).1)
    (hcomp : ∀ {X Y Z : R}, P.Rep X.1 Y.1 → P.Rep Y.1 Z.1 →
      ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + MP.radius X.1 Z.1 +
        MP.radius X.1 Y.1 + MP.radius Y.1 Z.1 + MQ.radius (obj X).1 (obj Z).1 ≤
          8 * MQ.radius (obj X).1 (obj Z).1)
    {X Y : R} (b : P.Rep X.1 Y.1) (θ : Q.Rep (obj X).1 (obj Y).1)
    (hθ : (Q.restrict D).ofRep (X := ⟨obj X⟩) (Y := ⟨obj Y⟩) θ =
      (relativeFunctor MP MQ obj bridge β ρ hbridge himprove hrespects hcomp).map
        ((P.restrict R).ofRep (X := ⟨X⟩) (Y := ⟨Y⟩) b)) :
    (MQ.val θ).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) <
      MQ.radius (obj X).1 (obj Y).1 + ρ X Y := by
  have hrel : Q.rel (obj X).1 (obj Y).1 θ
      (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) b) :=
    Quotient.exact (hθ.trans
      (relativeFunctor_map_ofRep MP MQ obj bridge β ρ hbridge himprove hrespects hcomp b))
  have hd := MQ.lt_of_rel hrel
  have hclose := transportRep_close MP MQ obj bridge ρ himprove (X := X) (Y := Y) b
  have htri := twoSidedDisagreement_le (MQ.val θ)
    (MQ.val (transportRep MP MQ obj bridge ρ himprove (X := X) (Y := Y) b))
    (sandwich (bridge X) (bridge Y) (MP.val b))
  omega

/-- **Connectivity.**  Two retained objects connected in the source groupoid have
images connected in the target groupoid. -/
theorem nonempty_hom_relativeFunctor
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (himprove : ∀ (X Y : R) (b : P.Rep X.1 Y.1), ∃ r : Q.Rep (obj X).1 (obj Y).1,
      (MQ.val r).twoSidedDisagreement (sandwich (bridge X) (bridge Y) (MP.val b)) < ρ X Y)
    (hrespects : ∀ {X Y : R}, P.Rep X.1 Y.1 →
      2 * ρ X Y + β X + β Y + MP.radius X.1 Y.1 ≤ 8 * MQ.radius (obj X).1 (obj Y).1)
    (hcomp : ∀ {X Y Z : R}, P.Rep X.1 Y.1 → P.Rep Y.1 Z.1 →
      ρ X Z + ρ X Y + ρ Y Z + 2 * β X + 2 * β Y + 2 * β Z + MP.radius X.1 Z.1 +
        MP.radius X.1 Y.1 + MP.radius Y.1 Z.1 + MQ.radius (obj X).1 (obj Z).1 ≤
          8 * MQ.radius (obj X).1 (obj Z).1)
    {X Y : R} (h : Nonempty ((⟨X.1⟩ : P.Obj) ⟶ ⟨Y.1⟩)) :
    Nonempty ((⟨(obj X).1⟩ : Q.Obj) ⟶ ⟨(obj Y).1⟩) :=
  h.elim fun a ↦
    ⟨(relativeFunctor MP MQ obj bridge β ρ hbridge himprove hrespects hcomp).map
      (X := ⟨X⟩) (Y := ⟨Y⟩) a⟩

end ClusterMetric
end GroupoidPresentation
end GroupApproximation
