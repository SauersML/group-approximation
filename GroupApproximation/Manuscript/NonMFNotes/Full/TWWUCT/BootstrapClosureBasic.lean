import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.NonUnitalHomotopy

/-!
# The class of algebras `KKn`-equivalent to commutative ones: basic layer

Rosenberg and Schochet (J. Rosenberg, C. Schochet, *The Künneth theorem and the universal
coefficient theorem for Kasparov's generalized K-functor*, Duke Math. J. 55 (1987), §§2--4;
see also Blackadar, *K-Theory for Operator Algebras*, §§22--23) study the class of separable
C⋆-algebras that are `KK`-equivalent to commutative ones.  Tu's theorem (amenable groups have
UCT reduced group C⋆-algebras), used for the Tikuisis--White--Winter input of
`thm:fixed-radical-membership` in `non_mf_group_notes.tex`, is proved by showing that proper
crossed products lie in this class and using its closure properties.

The algebras involved (suspensions, ideals, crossed products) are *non-unital*, so this file works
with separable non-unital C⋆-algebras (`SepNUCStarAlgebra`), and with `KKn`, the Cuntz picture of
Kasparov theory on non-unital algebras: `KKn(A, B)` is the set of homotopy classes of
`⋆`-homomorphisms `F A → F B` for the stabilized functor `F A = 𝒦 ⊗ qA` (J. Cuntz, *A new look at
KK-theory*, K-Theory 1 (1987)).  Since the product is composition, everything in this file only
uses the functoriality of `F`, which is bundled in `KKnFunctor`; the intended instance is the
functor `A ↦ Stab (Qalg A)` of lane TWWKK.

Contents:
* `KKnFunctor.KKnEquivalent`: an equivalence relation (`refl`, `symm`, `trans`), implied by
  `⋆`-isomorphism and by homotopy equivalence;
* `KKnFunctor.IsKKnCommutative`: `KKn`-equivalence to a separable commutative algebra, which
  contains the commutative algebras and is invariant under `KKn`-equivalence, `⋆`-isomorphism
  and homotopy equivalence.
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.Full.TWWKK

noncomputable section

/-- A separable non-unital complex C⋆-algebra, bundled with its instances. -/
structure SepNUCStarAlgebra where
  /-- The underlying type. -/
  carrier : Type
  [algebra : NonUnitalCStarAlgebra carrier]
  [separable : TopologicalSpace.SeparableSpace carrier]

attribute [instance] SepNUCStarAlgebra.algebra SepNUCStarAlgebra.separable

instance sepNUCStarAlgebraCoeSort : CoeSort SepNUCStarAlgebra Type :=
  ⟨SepNUCStarAlgebra.carrier⟩

/-- Bundle a separable non-unital C⋆-algebra. -/
def SepNUCStarAlgebra.of (A : Type) [NonUnitalCStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] : SepNUCStarAlgebra where
  carrier := A

/-- Commutativity of a bundled algebra. -/
def SepNUCStarAlgebra.IsCommutative (A : SepNUCStarAlgebra) : Prop :=
  ∀ x y : A, x * y = y * x

/-- **A stabilized homotopy functor on non-unital algebras** (Cuntz picture of `KKn`): an
assignment `A ↦ F A` of non-unital C⋆-algebras, functorial on non-unital `⋆`-homomorphisms and
sending homotopies to homotopies.  The intended model is `A ↦ 𝒦 ⊗ qA`. -/
structure KKnFunctor where
  /-- The object map. -/
  obj : SepNUCStarAlgebra → Type
  /-- The values are non-unital C⋆-algebras. -/
  [instObj : ∀ A : SepNUCStarAlgebra, NonUnitalCStarAlgebra (obj A)]
  /-- The morphism map. -/
  map : ∀ {A B : SepNUCStarAlgebra}, (A →⋆ₙₐ[ℂ] B) → (obj A →⋆ₙₐ[ℂ] obj B)
  /-- Identities go to identities. -/
  map_id : ∀ A : SepNUCStarAlgebra,
    map (NonUnitalStarAlgHom.id ℂ A) = NonUnitalStarAlgHom.id ℂ (obj A)
  /-- Composites go to composites. -/
  map_comp : ∀ {A B C : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] C),
    map (g.comp f) = (map g).comp (map f)
  /-- Homotopies go to homotopies. -/
  map_nHomotopic : ∀ {A B : SepNUCStarAlgebra} {f g : A →⋆ₙₐ[ℂ] B},
    NHomotopic f g → NHomotopic (map f) (map g)

attribute [instance] KKnFunctor.instObj

namespace KKnFunctor

variable (F : KKnFunctor)

/-- `KKn(A, B) = [F A, F B]`. -/
def Hom (A B : SepNUCStarAlgebra) : Type :=
  HomotopyClass (F.obj A) (F.obj B)

/-- The Kasparov product (composition); `F.comp y x` is "first `x`, then `y`". -/
def comp {A B C : SepNUCStarAlgebra} (y : F.Hom B C) (x : F.Hom A B) : F.Hom A C :=
  HomotopyClass.comp y x

/-- The unit class. -/
def idHom (A : SepNUCStarAlgebra) : F.Hom A A :=
  HomotopyClass.id (F.obj A)

/-- The class of a `⋆`-homomorphism. -/
def classOf {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B) : F.Hom A B :=
  HomotopyClass.mk (F.map f)

variable {F}

theorem comp_assoc {A B C D : SepNUCStarAlgebra} (z : F.Hom C D) (y : F.Hom B C)
    (x : F.Hom A B) : F.comp (F.comp z y) x = F.comp z (F.comp y x) :=
  HomotopyClass.comp_assoc z y x

theorem id_comp {A B : SepNUCStarAlgebra} (x : F.Hom A B) : F.comp (F.idHom B) x = x :=
  HomotopyClass.id_comp x

theorem comp_id {A B : SepNUCStarAlgebra} (x : F.Hom A B) : F.comp x (F.idHom A) = x :=
  HomotopyClass.comp_id x

theorem classOf_comp {A B C : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] C) :
    F.classOf (g.comp f) = F.comp (F.classOf g) (F.classOf f) := by
  show HomotopyClass.mk (F.map (g.comp f)) = HomotopyClass.mk ((F.map g).comp (F.map f))
  rw [F.map_comp f g]

theorem classOf_id (A : SepNUCStarAlgebra) :
    F.classOf (NonUnitalStarAlgHom.id ℂ A) = F.idHom A := by
  show HomotopyClass.mk (F.map (NonUnitalStarAlgHom.id ℂ A)) =
    HomotopyClass.mk (NonUnitalStarAlgHom.id ℂ (F.obj A))
  rw [F.map_id A]

theorem classOf_nHomotopic {A B : SepNUCStarAlgebra} {f g : A →⋆ₙₐ[ℂ] B}
    (h : NHomotopic f g) : F.classOf f = F.classOf g :=
  HomotopyClass.mk_eq_mk_of_nHomotopic (F.map_nHomotopic h)

variable (F)

/-- **`KKn`-equivalence**: classes both of whose products are the unit classes. -/
def KKnEquivalent (A B : SepNUCStarAlgebra) : Prop :=
  ∃ (x : F.Hom A B) (y : F.Hom B A), F.comp y x = F.idHom A ∧ F.comp x y = F.idHom B

variable {F}

theorem kknEquivalent_refl (A : SepNUCStarAlgebra) : F.KKnEquivalent A A :=
  ⟨F.idHom A, F.idHom A, id_comp _, id_comp _⟩

theorem KKnEquivalent.symm {A B : SepNUCStarAlgebra} (h : F.KKnEquivalent A B) :
    F.KKnEquivalent B A := by
  obtain ⟨x, y, hyx, hxy⟩ := h
  exact ⟨y, x, hxy, hyx⟩

theorem KKnEquivalent.trans {A B C : SepNUCStarAlgebra} (hAB : F.KKnEquivalent A B)
    (hBC : F.KKnEquivalent B C) : F.KKnEquivalent A C := by
  obtain ⟨x, y, hyx, hxy⟩ := hAB
  obtain ⟨z, w, hwz, hzw⟩ := hBC
  refine ⟨F.comp z x, F.comp y w, ?_, ?_⟩
  · calc F.comp (F.comp y w) (F.comp z x)
        = F.comp y (F.comp w (F.comp z x)) := comp_assoc y w (F.comp z x)
      _ = F.comp y (F.comp (F.comp w z) x) := by rw [comp_assoc w z x]
      _ = F.comp y (F.comp (F.idHom B) x) := by rw [hwz]
      _ = F.comp y x := by rw [id_comp x]
      _ = F.idHom A := hyx
  · calc F.comp (F.comp z x) (F.comp y w)
        = F.comp z (F.comp x (F.comp y w)) := comp_assoc z x (F.comp y w)
      _ = F.comp z (F.comp (F.comp x y) w) := by rw [comp_assoc x y w]
      _ = F.comp z (F.comp (F.idHom B) w) := by rw [hxy]
      _ = F.comp z w := by rw [id_comp w]
      _ = F.idHom C := hzw

/-- Two `⋆`-homomorphisms whose composites have the unit classes give a `KKn`-equivalence. -/
theorem kknEquivalent_of_comp_eq {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B)
    (g : B →⋆ₙₐ[ℂ] A) (hgf : F.classOf (g.comp f) = F.idHom A)
    (hfg : F.classOf (f.comp g) = F.idHom B) : F.KKnEquivalent A B := by
  refine ⟨F.classOf f, F.classOf g, ?_, ?_⟩
  · rw [← classOf_comp (F := F) f g]
    exact hgf
  · rw [← classOf_comp (F := F) g f]
    exact hfg

/-- **`⋆`-isomorphic algebras are `KKn`-equivalent.** -/
theorem kknEquivalent_of_inverse {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B)
    (g : B →⋆ₙₐ[ℂ] A) (hgf : ∀ a : A, g (f a) = a) (hfg : ∀ b : B, f (g b) = b) :
    F.KKnEquivalent A B := by
  refine kknEquivalent_of_comp_eq f g ?_ ?_
  · rw [show g.comp f = NonUnitalStarAlgHom.id ℂ A from by ext a; exact hgf a]
    exact classOf_id A
  · rw [show f.comp g = NonUnitalStarAlgHom.id ℂ B from by ext b; exact hfg b]
    exact classOf_id B

/-- **Homotopy equivalent algebras are `KKn`-equivalent.** -/
theorem kknEquivalent_of_homotopyEquiv {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B)
    (g : B →⋆ₙₐ[ℂ] A) (hgf : NHomotopic (g.comp f) (NonUnitalStarAlgHom.id ℂ A))
    (hfg : NHomotopic (f.comp g) (NonUnitalStarAlgHom.id ℂ B)) : F.KKnEquivalent A B := by
  refine kknEquivalent_of_comp_eq f g ?_ ?_
  · rw [classOf_nHomotopic (F := F) hgf]
    exact classOf_id A
  · rw [classOf_nHomotopic (F := F) hfg]
    exact classOf_id B

variable (F)

/-- **`IsKKnCommutative`**: `A` is `KKn`-equivalent to a separable commutative C⋆-algebra
(Rosenberg--Schochet 1987, §4; Blackadar 22.3.4). -/
def IsKKnCommutative (A : SepNUCStarAlgebra) : Prop :=
  ∃ C : SepNUCStarAlgebra, C.IsCommutative ∧ F.KKnEquivalent A C

variable {F}

/-- Commutative algebras are in the class. -/
theorem isKKnCommutative_of_isCommutative {A : SepNUCStarAlgebra} (hA : A.IsCommutative) :
    F.IsKKnCommutative A :=
  ⟨A, hA, kknEquivalent_refl A⟩

/-- **Invariance under `KKn`-equivalence.** -/
theorem IsKKnCommutative.of_kknEquivalent {A B : SepNUCStarAlgebra} (hA : F.IsKKnCommutative A)
    (h : F.KKnEquivalent A B) : F.IsKKnCommutative B := by
  obtain ⟨C, hC, hAC⟩ := hA
  exact ⟨C, hC, KKnEquivalent.trans (KKnEquivalent.symm h) hAC⟩

theorem isKKnCommutative_iff_of_kknEquivalent {A B : SepNUCStarAlgebra}
    (h : F.KKnEquivalent A B) : F.IsKKnCommutative A ↔ F.IsKKnCommutative B :=
  ⟨fun hA => hA.of_kknEquivalent h, fun hB => hB.of_kknEquivalent (KKnEquivalent.symm h)⟩

/-- Invariance under `⋆`-isomorphism. -/
theorem IsKKnCommutative.of_inverse {A B : SepNUCStarAlgebra} (hA : F.IsKKnCommutative A)
    (f : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] A) (hgf : ∀ a : A, g (f a) = a)
    (hfg : ∀ b : B, f (g b) = b) : F.IsKKnCommutative B :=
  hA.of_kknEquivalent (kknEquivalent_of_inverse f g hgf hfg)

/-- Invariance under homotopy equivalence. -/
theorem IsKKnCommutative.of_homotopyEquiv {A B : SepNUCStarAlgebra} (hA : F.IsKKnCommutative A)
    (f : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] A)
    (hgf : NHomotopic (g.comp f) (NonUnitalStarAlgHom.id ℂ A))
    (hfg : NHomotopic (f.comp g) (NonUnitalStarAlgHom.id ℂ B)) : F.IsKKnCommutative B :=
  hA.of_kknEquivalent (kknEquivalent_of_homotopyEquiv f g hgf hfg)

end KKnFunctor

end

end GroupApproximation.Full.TWWUCT.Bootstrap
