import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapMinTensorMap
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureFunctorial

/-!
# The minimal tensor product as a bifunctor on homotopy classes

The minimal tensor product is functorial on classes (Blackadar, *K-Theory for Operator Algebras*,
18.9; Rosenberg--Schochet, Duke Math. J. 55 (1987), §2).  So the class of algebras equivalent to
commutative ones is closed under `⊗_min`, and under `· ⊗_min C` for commutative `C`.  This file
proves that step for the homotopy functor `A ↦ A`, whose classes `[A, B]` are homotopy classes of
`⋆`-homomorphisms.

* `MinTensor.mapClass x y : [A ⊗_min C, A' ⊗_min C']` for classes `x : [A, A']` and
  `y : [C, C']`, well defined by `MinTensor.nHomotopic_map`, with `mapClass_id` and
  `mapClass_comp`;
* `KKnBifunctor.rightEndo P C`: a bifunctor with its second variable fixed at `C` is an
  endofunctor;
* `homotopyFunctor : KKnFunctor`, the identity on objects and on `⋆`-homomorphisms;
* `minTensorBifunctor : KKnBifunctor homotopyFunctor` with `objOp := SepNUCStarAlgebra.minTensor`,
  and `minTensorRightEndo C : KKnEndo homotopyFunctor` for `A ↦ A ⊗_min C`;
* the corollaries `kknEquivalent_minTensor`, `isKKnCommutative_minTensor`,
  `isKKnCommutative_minTensor_right` and `isKKnCommutative_foldr_minTensor`.

The instance for Cuntz's functor `A ↦ 𝒦 ⊗ qA` needs `q(A ⊗ C) → qA ⊗ C`, `qA ∼ A` and
`𝒦 ⊗ 𝒦 ≅ 𝒦`, which come from the KK lanes.

Manuscript: `non_mf_group_notes.tex`, UCT input of `thm:fixed-radical-membership`
(lane TWWUCT-F3, work order WO-TWWUCT-F-3).
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.Full.TWWKK

noncomputable section

namespace MinTensor

section MapClass

variable {A A' A'' C C' C'' : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra C']
  [NonUnitalCStarAlgebra C'']

/-- **The minimal tensor product of homotopy classes**, `[f] ⊗ [g] = [f ⊗ g]`. -/
def mapClass (x : HomotopyClass A A') (y : HomotopyClass C C') :
    HomotopyClass (closed A C) (closed A' C') :=
  Quot.lift
    (fun f : A →⋆ₙₐ[ℂ] A' =>
      Quot.lift (fun g : C →⋆ₙₐ[ℂ] C' => HomotopyClass.mk (MinTensor.map f g))
        (fun _ _ h =>
          HomotopyClass.mk_eq_mk_of_nHomotopic
            (MinTensor.nHomotopic_map (NHomotopic.refl f) h)) y)
    (fun _ _ h => by
      induction y using HomotopyClass.ind with
      | mk g =>
        exact HomotopyClass.mk_eq_mk_of_nHomotopic
          (MinTensor.nHomotopic_map h (NHomotopic.refl g)))
    x

theorem mapClass_mk (f : A →⋆ₙₐ[ℂ] A') (g : C →⋆ₙₐ[ℂ] C') :
    mapClass (HomotopyClass.mk f) (HomotopyClass.mk g) = HomotopyClass.mk (MinTensor.map f g) :=
  rfl

/-- **Identity classes go to the identity class.** -/
theorem mapClass_id :
    mapClass (HomotopyClass.id A) (HomotopyClass.id C) = HomotopyClass.id (closed A C) := by
  show HomotopyClass.mk (MinTensor.map (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ C))
    = HomotopyClass.mk (NonUnitalStarAlgHom.id ℂ (closed A C))
  rw [MinTensor.map_id]

/-- **Products of classes go to products.** -/
theorem mapClass_comp (x' : HomotopyClass A' A'') (x : HomotopyClass A A')
    (y' : HomotopyClass C' C'') (y : HomotopyClass C C') :
    mapClass (HomotopyClass.comp x' x) (HomotopyClass.comp y' y) =
      HomotopyClass.comp (mapClass x' y') (mapClass x y) := by
  induction x using HomotopyClass.ind with
  | mk f =>
    induction x' using HomotopyClass.ind with
    | mk f' =>
      induction y using HomotopyClass.ind with
      | mk g =>
        induction y' using HomotopyClass.ind with
        | mk g' =>
          show HomotopyClass.mk (MinTensor.map (f'.comp f) (g'.comp g)) =
            HomotopyClass.mk ((MinTensor.map f' g').comp (MinTensor.map f g))
          rw [MinTensor.map_comp]

end MapClass

end MinTensor

namespace KKnBifunctor

variable {F : KKnFunctor} (P : KKnBifunctor F)

/-- **A bifunctor with its second variable fixed** at `E`: the endofunctor `A ↦ P A E`, acting on
classes by `x ↦ P x 1_E`. -/
def rightEndo (E : SepNUCStarAlgebra) : KKnEndo F where
  objOp X := P.objOp X E
  homOp u := P.homOp u (F.idHom E)
  homOp_id X := P.homOp_id X E
  homOp_comp v u := by
    have h : F.comp (F.idHom E) (F.idHom E) = F.idHom E := KKnFunctor.id_comp (F.idHom E)
    calc P.homOp (F.comp v u) (F.idHom E)
        = P.homOp (F.comp v u) (F.comp (F.idHom E) (F.idHom E)) := by rw [h]
      _ = F.comp (P.homOp v (F.idHom E)) (P.homOp u (F.idHom E)) :=
          P.homOp_comp v u (F.idHom E) (F.idHom E)

theorem rightEndo_objOp (E X : SepNUCStarAlgebra) : (P.rightEndo E).objOp X = P.objOp X E :=
  rfl

end KKnBifunctor

/-- **The homotopy functor** `A ↦ A`: its classes `[A, B]` are the homotopy classes of
`⋆`-homomorphisms `A → B`. -/
def homotopyFunctor : KKnFunctor where
  obj A := A.carrier
  instObj A := A.algebra
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
  map_nHomotopic h := h

/-- `[f] ⊗ [g]` on the classes of the homotopy functor. -/
def minTensorHomOp {A A' B B' : SepNUCStarAlgebra} (x : homotopyFunctor.Hom A A')
    (y : homotopyFunctor.Hom B B') : homotopyFunctor.Hom (A.minTensor B) (A'.minTensor B') :=
  MinTensor.mapClass (A := A) (A' := A') (C := B) (C' := B') x y

theorem minTensorHomOp_id (A B : SepNUCStarAlgebra) :
    minTensorHomOp (homotopyFunctor.idHom A) (homotopyFunctor.idHom B) =
      homotopyFunctor.idHom (A.minTensor B) :=
  MinTensor.mapClass_id (A := A) (C := B)

theorem minTensorHomOp_comp {A A' A'' B B' B'' : SepNUCStarAlgebra}
    (x' : homotopyFunctor.Hom A' A'') (x : homotopyFunctor.Hom A A')
    (y' : homotopyFunctor.Hom B' B'') (y : homotopyFunctor.Hom B B') :
    minTensorHomOp (homotopyFunctor.comp x' x) (homotopyFunctor.comp y' y) =
      homotopyFunctor.comp (minTensorHomOp x' y') (minTensorHomOp x y) :=
  MinTensor.mapClass_comp (A := A) (A' := A') (A'' := A'') (C := B) (C' := B') (C'' := B'')
    x' x y' y

/-- **The minimal tensor product bifunctor** `(A, B) ↦ A ⊗_min B` on the homotopy functor. -/
def minTensorBifunctor : KKnBifunctor homotopyFunctor where
  objOp := SepNUCStarAlgebra.minTensor
  homOp x y := minTensorHomOp x y
  homOp_id := minTensorHomOp_id
  homOp_comp := minTensorHomOp_comp

theorem minTensorBifunctor_objOp (A B : SepNUCStarAlgebra) :
    minTensorBifunctor.objOp A B = A.minTensor B :=
  rfl

/-- **Tensoring with a fixed algebra** `A ↦ A ⊗_min C`, as an endofunctor. -/
def minTensorRightEndo (C : SepNUCStarAlgebra) : KKnEndo homotopyFunctor :=
  minTensorBifunctor.rightEndo C

theorem minTensorRightEndo_objOp (C A : SepNUCStarAlgebra) :
    (minTensorRightEndo C).objOp A = A.minTensor C :=
  rfl

section Corollaries

/-- **Equivalence is compatible with minimal tensor products.** -/
theorem kknEquivalent_minTensor {A A' B B' : SepNUCStarAlgebra}
    (hA : homotopyFunctor.KKnEquivalent A A') (hB : homotopyFunctor.KKnEquivalent B B') :
    homotopyFunctor.KKnEquivalent (A.minTensor B) (A'.minTensor B') :=
  minTensorBifunctor.kknEquivalent hA hB

/-- **Closure under minimal tensor products** (Rosenberg--Schochet 1987, §2; Blackadar
22.3.5). -/
theorem isKKnCommutative_minTensor {A B : SepNUCStarAlgebra}
    (hA : homotopyFunctor.IsKKnCommutative A) (hB : homotopyFunctor.IsKKnCommutative B) :
    homotopyFunctor.IsKKnCommutative (A.minTensor B) :=
  minTensorBifunctor.isKKnCommutative
    (fun _ _ hC hD => SepNUCStarAlgebra.IsCommutative.minTensor hC hD) hA hB

/-- **Closure under tensoring with a commutative algebra** `A ↦ A ⊗_min C`. -/
theorem isKKnCommutative_minTensor_right {C : SepNUCStarAlgebra} (hC : C.IsCommutative)
    {A : SepNUCStarAlgebra} (hA : homotopyFunctor.IsKKnCommutative A) :
    homotopyFunctor.IsKKnCommutative (A.minTensor C) :=
  (minTensorRightEndo C).isKKnCommutative
    (fun _ hD => SepNUCStarAlgebra.IsCommutative.minTensor hD hC) hA

/-- **Closure under finite minimal tensor products** `A₁ ⊗ (A₂ ⊗ (⋯ ⊗ Z))`. -/
theorem isKKnCommutative_foldr_minTensor {Z : SepNUCStarAlgebra}
    (hZ : homotopyFunctor.IsKKnCommutative Z) (L : List SepNUCStarAlgebra)
    (hL : ∀ A ∈ L, homotopyFunctor.IsKKnCommutative A) :
    homotopyFunctor.IsKKnCommutative (L.foldr SepNUCStarAlgebra.minTensor Z) :=
  minTensorBifunctor.isKKnCommutative_foldr
    (fun _ _ hC hD => SepNUCStarAlgebra.IsCommutative.minTensor hC hD) hZ L hL

end Corollaries

end

end GroupApproximation.Full.TWWUCT.Bootstrap
