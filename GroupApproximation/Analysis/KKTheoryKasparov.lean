import GroupApproximation.Analysis.CStarExactness
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# `KK`-theory: the Kasparov bifunctor, and what follows from its axioms

Kasparov's bivariant `K`-theory assigns to a pair `(A, B)` of separable
C⋆-algebras an abelian group `KK(A, B)`, contravariantly functorial in `A`,
covariantly in `B`, homotopy invariant in both, and equipped with an
associative *Kasparov product*
`KK(A, B) × KK(B, C) → KK(A, C)` with units.  It is the value group in which
the universal coefficient theorem and the Dadarlat--Eilers uniqueness theorem
are stated, and it is the reason the UCT hypothesis appears in
Tikuisis--White--Winter at all.

## What this file is, exactly

`KK(A, B)` is **not constructed here.**  Its construction --- Kasparov
bimodules over Hilbert C⋆-modules, the stabilization theorem, and the
technical theorem producing the product --- is a body of analysis with no
counterpart in mathlib: there are no Hilbert C⋆-modules, no multiplier
algebras, no Fredholm theory over a C⋆-algebra.  Claiming a construction here
would be false.

What is done instead is what can be done honestly, and is what the downstream
statements actually consume: **`KasparovTheory` bundles the bifunctor together
with its axioms, and everything below is proved from those axioms with no
further assumption.**  A `KasparovTheory` is a structure, so every theorem
that uses `KK`-theory carries a visible binder saying so, in exactly the
discipline `Analysis.TikuisisWhiteWinter` uses for its inputs.  Nothing in
this development constructs an inhabitant, and nothing may: an inhabitant is
Kasparov's theorem.

The axioms taken are the minimal ones the rest of the chain uses:

1. `Grp A B` is an abelian group;
2. the product is associative and unital;
3. a `⋆`-homomorphism has a class, functorially;
4. homotopic `⋆`-homomorphisms have equal classes.

Bilinearity of the product is *not* a field --- it is a separate predicate
`IsBilinear`, assumed only by the two theorems that need it --- and
stability, split exactness and Bott periodicity are not assumed at all.  They
are true of `KK`, but nothing downstream needs them, and an unused axiom is an
unnecessary strengthening of every theorem below.

## What is proved, unconditionally, from those axioms

* `KKEquivalent` is reflexive, symmetric and transitive, the symmetry and
  transitivity being genuine consequences of associativity and unitality
  rather than definitional;
* algebras carrying mutually inverse `⋆`-homomorphisms are `KK`-equivalent;
* **homotopy equivalent algebras are `KK`-equivalent** --- this is where
  homotopy invariance earns its place, and it is the mechanism by which the
  bootstrap class is closed under the operations that build it.

## Separability

`KK` is a bifunctor on separable C⋆-algebras (the product needs separability
of the first variable), so the objects are bundled *with* separability, in
`SepCStarAlgebra`.  Every algebra the Tikuisis--White--Winter route applies
this to is separable --- that is one of the four hypotheses of the theorem ---
so nothing is lost, and asserting `KK` only where it exists keeps the assumed
structure from being stronger than the mathematics.
-/

namespace GroupApproximation
namespace KK

universe u

noncomputable section

/-! ## Objects -/

/-- A separable complex C⋆-algebra, bundled with its instances.  This is the
object type of the Kasparov category. -/
structure SepCStarAlgebra where
  /-- The underlying type. -/
  carrier : Type u
  [algebra : CStarAlgebra carrier]
  [separable : TopologicalSpace.SeparableSpace carrier]

attribute [instance] SepCStarAlgebra.algebra SepCStarAlgebra.separable

instance sepCStarAlgebraCoeSort : CoeSort SepCStarAlgebra.{u} (Type u) :=
  ⟨SepCStarAlgebra.carrier⟩

/-- Commutativity of a bundled algebra.  The bootstrap class is defined by
`KK`-equivalence to a *commutative* algebra, so this predicate is part of the
statement of the UCT. -/
def SepCStarAlgebra.IsCommutative (A : SepCStarAlgebra.{u}) : Prop :=
  ∀ x y : A, x * y = y * x

/-- `ℂ`, as an object of the Kasparov category.  It is the unit of the
product, and the algebra whose `KK`-groups are ordinary `K`-theory. -/
def complexAlgebra : SepCStarAlgebra.{0} where
  carrier := ℂ

theorem complexAlgebra_isCommutative : complexAlgebra.IsCommutative :=
  fun x y => mul_comm x y

/-! ## Homotopy of `⋆`-homomorphisms -/

/-- **Homotopy of `⋆`-homomorphisms**: a path of `⋆`-homomorphisms, continuous
pointwise, joining `f` to `g`.

Stated pointwise rather than as a single `⋆`-homomorphism into `C([0,1], B)`
so that no C⋆-structure on a mapping space is required; the two formulations
agree, and the pointwise one is what a construction produces. -/
def Homotopic {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f g : A →⋆ₐ[ℂ] B) : Prop :=
  ∃ p : ℝ → (A →⋆ₐ[ℂ] B),
    (∀ a : A, Continuous fun t : ℝ => p t a) ∧ p 0 = f ∧ p 1 = g

theorem Homotopic.refl {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) : Homotopic f f :=
  ⟨fun _ => f, fun _ => continuous_const, rfl, rfl⟩

theorem Homotopic.symm {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {f g : A →⋆ₐ[ℂ] B} (h : Homotopic f g) : Homotopic g f := by
  obtain ⟨p, hp, h0, h1⟩ := h
  refine ⟨fun t => p (1 - t),
    fun a => (hp a).comp (continuous_const.sub continuous_id), ?_, ?_⟩
  · rw [sub_zero]; exact h1
  · rw [sub_self]; exact h0

/-! ## The Kasparov bifunctor -/

/-- **A model of Kasparov's `KK`-theory**, as a bundled structure.

Consuming this structure is consuming Kasparov's theorem; no inhabitant is
constructed in this development.  See the module docstring for why the axiom
list is exactly this long. -/
structure KasparovTheory where
  /-- The `KK`-group of a pair. -/
  Grp : SepCStarAlgebra.{u} → SepCStarAlgebra.{u} → Type u
  /-- **The Kasparov product.** -/
  product : ∀ {A B C : SepCStarAlgebra.{u}}, Grp A B → Grp B C → Grp A C
  /-- The product is associative. -/
  product_assoc : ∀ {A B C D : SepCStarAlgebra.{u}}
    (x : Grp A B) (y : Grp B C) (z : Grp C D),
    product (product x y) z = product x (product y z)
  /-- The identity class. -/
  unit : ∀ A : SepCStarAlgebra.{u}, Grp A A
  /-- The identity class is a left unit. -/
  unit_product : ∀ {A B : SepCStarAlgebra.{u}} (x : Grp A B),
    product (unit A) x = x
  /-- The identity class is a right unit. -/
  product_unit : ∀ {A B : SepCStarAlgebra.{u}} (x : Grp A B),
    product x (unit B) = x
  /-- The class of a `⋆`-homomorphism. -/
  classOf : ∀ {A B : SepCStarAlgebra.{u}}, (A →⋆ₐ[ℂ] B) → Grp A B
  /-- The class of the identity is the unit. -/
  classOf_id : ∀ A : SepCStarAlgebra.{u},
    classOf (StarAlgHom.id ℂ A) = unit A
  /-- Functoriality: the class of a composite is the product of the classes. -/
  classOf_comp : ∀ {A B C : SepCStarAlgebra.{u}} (f : A →⋆ₐ[ℂ] B)
    (g : B →⋆ₐ[ℂ] C), classOf (g.comp f) = product (classOf f) (classOf g)
  /-- **Homotopy invariance.** -/
  classOf_homotopic : ∀ {A B : SepCStarAlgebra.{u}} {f g : A →⋆ₐ[ℂ] B},
    Homotopic f g → classOf f = classOf g
  /-- Each `KK`-group is an abelian group.  Declared last so that the axioms
  above do not have to mention it; bilinearity of the product is the separate
  predicate `IsBilinear`. -/
  addCommGroup : ∀ A B : SepCStarAlgebra.{u}, AddCommGroup (Grp A B)

attribute [instance] KasparovTheory.addCommGroup

namespace KasparovTheory

variable (T : KasparovTheory.{u})

/-- **Bilinearity of the Kasparov product.**  A separate predicate rather than
a field of `KasparovTheory`: a field would have to be stated before the group
structure is available as an instance, and only the `K`-theoretic
functoriality of `Analysis.KKTheoryKGroups` consumes it. -/
def IsBilinear : Prop :=
  ∀ {A B C : SepCStarAlgebra.{u}} (x x' : T.Grp A B) (y y' : T.Grp B C),
    T.product (x + x') y = T.product x y + T.product x' y ∧
      T.product x (y + y') = T.product x y + T.product x y'

/-! ## `KK`-equivalence -/

/-- **`KK`-equivalence**: two classes whose products both ways are the
identity classes.  This is the equivalence relation the bootstrap class is
defined up to, and the relation under which the UCT hypothesis of
Tikuisis--White--Winter is invariant. -/
def KKEquivalent (A B : SepCStarAlgebra.{u}) : Prop :=
  ∃ (x : T.Grp A B) (y : T.Grp B A),
    T.product x y = T.unit A ∧ T.product y x = T.unit B

variable {T}

theorem kkEquivalent_refl (A : SepCStarAlgebra.{u}) : T.KKEquivalent A A :=
  ⟨T.unit A, T.unit A, T.unit_product _, T.unit_product _⟩

theorem KKEquivalent.symm {A B : SepCStarAlgebra.{u}}
    (h : T.KKEquivalent A B) : T.KKEquivalent B A := by
  obtain ⟨x, y, hxy, hyx⟩ := h
  exact ⟨y, x, hyx, hxy⟩

/-- **`KK`-equivalence is transitive.**  The witnesses compose, and the proof
is the associativity and unitality of the Kasparov product --- this is the
first place the product does genuine work. -/
theorem KKEquivalent.trans {A B C : SepCStarAlgebra.{u}}
    (hAB : T.KKEquivalent A B) (hBC : T.KKEquivalent B C) :
    T.KKEquivalent A C := by
  obtain ⟨x, y, hxy, hyx⟩ := hAB
  obtain ⟨z, w, hzw, hwz⟩ := hBC
  refine ⟨T.product x z, T.product w y, ?_, ?_⟩
  · calc T.product (T.product x z) (T.product w y)
        = T.product x (T.product z (T.product w y)) :=
          T.product_assoc x z (T.product w y)
      _ = T.product x (T.product (T.product z w) y) := by
          rw [T.product_assoc z w y]
      _ = T.product x (T.product (T.unit B) y) := by rw [hzw]
      _ = T.product x y := by rw [T.unit_product y]
      _ = T.unit A := hxy
  · calc T.product (T.product w y) (T.product x z)
        = T.product w (T.product y (T.product x z)) :=
          T.product_assoc w y (T.product x z)
      _ = T.product w (T.product (T.product y x) z) := by
          rw [T.product_assoc y x z]
      _ = T.product w (T.product (T.unit B) z) := by rw [hyx]
      _ = T.product w z := by rw [T.unit_product z]
      _ = T.unit C := hwz

/-! ## Isomorphism and homotopy equivalence both imply `KK`-equivalence -/

/-- Two `⋆`-homomorphisms whose composites have the identity classes give a
`KK`-equivalence.  This is the workhorse: both corollaries below are instances
of it. -/
theorem kkEquivalent_of_comp_eq {A B : SepCStarAlgebra.{u}}
    (f : A →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] A)
    (hgf : T.classOf (g.comp f) = T.unit A)
    (hfg : T.classOf (f.comp g) = T.unit B) :
    T.KKEquivalent A B := by
  refine ⟨T.classOf f, T.classOf g, ?_, ?_⟩
  · rw [← T.classOf_comp f g]; exact hgf
  · rw [← T.classOf_comp g f]; exact hfg

/-- **Isomorphic algebras are `KK`-equivalent.**  Stated with the inverse pair
spelled out rather than through `StarAlgEquiv`, so that the theorem applies
verbatim to a pair of maps that happen to be mutually inverse without anyone
having to bundle them first. -/
theorem kkEquivalent_of_inverse {A B : SepCStarAlgebra.{u}}
    (f : A →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] A)
    (hgf : ∀ a : A, g (f a) = a) (hfg : ∀ b : B, f (g b) = b) :
    T.KKEquivalent A B := by
  refine kkEquivalent_of_comp_eq f g ?_ ?_
  · rw [show g.comp f = StarAlgHom.id ℂ A from by ext a; exact hgf a]
    exact T.classOf_id A
  · rw [show f.comp g = StarAlgHom.id ℂ B from by ext b; exact hfg b]
    exact T.classOf_id B

/-- **Homotopy equivalent algebras are `KK`-equivalent.**

This is strictly stronger than the isomorphism case, and it is the closure
property the bootstrap class is built from: a deformation retraction of
C⋆-algebras --- a cone onto its base point, an algebra onto a corner --- is
almost never an isomorphism, and is always a `KK`-equivalence. -/
theorem kkEquivalent_of_homotopyEquiv {A B : SepCStarAlgebra.{u}}
    (f : A →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] A)
    (hgf : Homotopic (g.comp f) (StarAlgHom.id ℂ A))
    (hfg : Homotopic (f.comp g) (StarAlgHom.id ℂ B)) :
    T.KKEquivalent A B := by
  refine kkEquivalent_of_comp_eq f g ?_ ?_
  · rw [T.classOf_homotopic hgf]; exact T.classOf_id A
  · rw [T.classOf_homotopic hfg]; exact T.classOf_id B

end KasparovTheory

end

end KK
end GroupApproximation
