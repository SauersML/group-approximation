import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.NonUnitalHomotopy

/-!
# Kasparov theories from stabilized homotopy functors

In Cuntz's picture of Kasparov theory (J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987)
31--51, §§1--3; see also Blackadar, *K-Theory for Operator Algebras*, ch. VIII and §17.8),
`KK(A, B)` is the set of homotopy classes of `⋆`-homomorphisms `𝒦 ⊗ qA → 𝒦 ⊗ qB`, and the
Kasparov product is composition.  This file isolates the formal part of that picture.

A `StableFunctor` is an assignment `A ↦ F A` of non-unital C⋆-algebras to separable unital
C⋆-algebras, functorial on unital `⋆`-homomorphisms and sending homotopies to homotopies.
Given an abelian group structure on the homotopy classes `F.Hom A B = [F A, F B]`,
`toKasparovTheory` produces a `KK.KasparovTheory`: product = composition, unit = identity
class, `classOf f = [F f]`.  Every axiom is formal.  Bilinearity of the product is exactly
bilinearity of composition (`CompBilinear`), see `toKasparovTheory_isBilinear`.

The genuine content (the functor `A ↦ 𝒦 ⊗ qA`, the Cuntz sum group structure, bilinearity, and
`KK(ℂ, ℂ) ≅ ℤ`) is supplied separately; nothing here is a trivial model.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`.
-/

namespace GroupApproximation.Full.TWWKK

noncomputable section

/-- **A stabilized homotopy functor** on separable unital C⋆-algebras with values in
non-unital C⋆-algebras (the intended model is `A ↦ 𝒦 ⊗ qA`). -/
structure StableFunctor where
  /-- The object map. -/
  obj : KK.SepCStarAlgebra.{0} → Type
  /-- The values are non-unital C⋆-algebras. -/
  [instObj : ∀ A : KK.SepCStarAlgebra.{0}, NonUnitalCStarAlgebra (obj A)]
  /-- The morphism map, on unital `⋆`-homomorphisms. -/
  map : ∀ {A B : KK.SepCStarAlgebra.{0}}, (A →⋆ₐ[ℂ] B) → (obj A →⋆ₙₐ[ℂ] obj B)
  /-- Identities go to identities. -/
  map_id : ∀ A : KK.SepCStarAlgebra.{0},
    map (StarAlgHom.id ℂ A) = NonUnitalStarAlgHom.id ℂ (obj A)
  /-- Composites go to composites. -/
  map_comp : ∀ {A B C : KK.SepCStarAlgebra.{0}} (f : A →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] C),
    map (g.comp f) = (map g).comp (map f)
  /-- Homotopies go to homotopies. -/
  map_homotopic : ∀ {A B : KK.SepCStarAlgebra.{0}} {f g : A →⋆ₐ[ℂ] B},
    KK.Homotopic f g → NHomotopic (map f) (map g)

attribute [instance] StableFunctor.instObj

namespace StableFunctor

variable (F : StableFunctor)

/-- The morphism sets of the homotopy category: `[F A, F B]`. -/
def Hom (A B : KK.SepCStarAlgebra.{0}) : Type :=
  HomotopyClass (F.obj A) (F.obj B)

/-- Composition in the homotopy category, typed through `Hom` so that instances on `Hom`
apply to its values.  `F.comp y x` is "first `x`, then `y`". -/
def comp {A B C : KK.SepCStarAlgebra.{0}} (y : F.Hom B C) (x : F.Hom A B) : F.Hom A C :=
  HomotopyClass.comp y x

/-- **Bilinearity of composition** with respect to given group structures on the morphism
sets. -/
def CompBilinear [∀ A B, AddCommGroup (F.Hom A B)] : Prop :=
  ∀ {A B C : KK.SepCStarAlgebra.{0}} (x x' : F.Hom A B) (y y' : F.Hom B C),
    F.comp y (x + x') = F.comp y x + F.comp y x' ∧
      F.comp (y + y') x = F.comp y x + F.comp y' x

/-- **The Kasparov theory of a stabilized homotopy functor**: `Grp A B = [F A, F B]`, the
product is composition, and `classOf f = [F f]`. -/
def toKasparovTheory [∀ A B, AddCommGroup (F.Hom A B)] : KK.KasparovTheory.{0} where
  Grp := F.Hom
  product x y := F.comp y x
  product_assoc x y z := (HomotopyClass.comp_assoc z y x).symm
  unit A := HomotopyClass.id (F.obj A)
  unit_product x := HomotopyClass.comp_id x
  product_unit x := HomotopyClass.id_comp x
  classOf f := HomotopyClass.mk (F.map f)
  classOf_id A := by
    show HomotopyClass.mk (F.map (StarAlgHom.id ℂ A)) =
      HomotopyClass.mk (NonUnitalStarAlgHom.id ℂ (F.obj A))
    rw [F.map_id]
  classOf_comp f g := by
    show HomotopyClass.mk (F.map (g.comp f)) = HomotopyClass.mk ((F.map g).comp (F.map f))
    rw [F.map_comp]
  classOf_homotopic h := HomotopyClass.mk_eq_mk_of_nHomotopic (F.map_homotopic h)
  addCommGroup A B := inferInstanceAs (AddCommGroup (F.Hom A B))

theorem toKasparovTheory_grp [∀ A B, AddCommGroup (F.Hom A B)]
    (A B : KK.SepCStarAlgebra.{0}) : F.toKasparovTheory.Grp A B = F.Hom A B :=
  rfl

/-- Bilinear composition gives a bilinear Kasparov product. -/
theorem toKasparovTheory_isBilinear [∀ A B, AddCommGroup (F.Hom A B)] (h : F.CompBilinear) :
    F.toKasparovTheory.IsBilinear := by
  intro _ _ _ x x' y y'
  exact h x x' y y'

/-- An additive identification of a morphism group transfers to the Kasparov group. -/
def toKasparovTheoryAddEquiv [∀ A B, AddCommGroup (F.Hom A B)]
    {A B : KK.SepCStarAlgebra.{0}} {G : Type*} [AddCommGroup G] (e : F.Hom A B ≃+ G) :
    F.toKasparovTheory.Grp A B ≃+ G :=
  e

end StableFunctor

end

end GroupApproximation.Full.TWWKK
