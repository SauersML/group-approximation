import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureBasic

/-!
# Closure of `IsKKnCommutative` under `KKn`-functorial constructions

Rosenberg--Schochet (Duke Math. J. 55 (1987), §2) and Blackadar (*K-Theory for Operator
Algebras*, 22.3.4--22.3.5) note that the class of algebras `KK`-equivalent to commutative ones is
closed under every construction that is functorial on `KK`-classes and sends commutative algebras
into the class: suspension `A ↦ C₀(ℝ, A)`, finite direct sums, and minimal tensor products
(Kasparov's external product makes `⊗` a `KK`-bifunctor).  This file proves that formal part:

* `KKnEndo F`: a construction on objects together with a functorial action on `KKn`-classes
  (the intended instances are suspension and tensoring with a fixed algebra); it preserves
  `KKn`-equivalence (`KKnEndo.kknEquivalent`) and, when it sends commutative algebras into the
  class, preserves the class (`KKnEndo.isKKnCommutative`);
* `KKnBifunctor F`: the same for two variables (direct sum, minimal tensor product):
  `KKnBifunctor.kknEquivalent`, `KKnBifunctor.isKKnCommutative`, and iterated (finite) sums or
  products `KKnBifunctor.isKKnCommutative_foldr`;
* the concrete direct sum `SepNUCStarAlgebra.prod` with `IsCommutative.prod`.

The action on classes for the concrete functor `A ↦ 𝒦 ⊗ qA` is supplied by the KK lanes.

Manuscript: `non_mf_group_notes.tex`, UCT input of `thm:fixed-radical-membership`.
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.Full.TWWKK

noncomputable section

/-- The direct sum `A ⊕ B` of two separable non-unital C⋆-algebras. -/
def SepNUCStarAlgebra.prod (A B : SepNUCStarAlgebra) : SepNUCStarAlgebra where
  carrier := A × B

/-- A direct sum of commutative algebras is commutative. -/
theorem SepNUCStarAlgebra.IsCommutative.prod {A B : SepNUCStarAlgebra} (hA : A.IsCommutative)
    (hB : B.IsCommutative) : (A.prod B).IsCommutative :=
  fun x y => Prod.ext (hA (Prod.fst x) (Prod.fst y)) (hB (Prod.snd x) (Prod.snd y))

/-- **A `KKn`-endofunctor**: an object map with a functorial action on `KKn`-classes. -/
structure KKnEndo (F : KKnFunctor) where
  /-- The object map. -/
  objOp : SepNUCStarAlgebra → SepNUCStarAlgebra
  /-- The action on classes. -/
  homOp : ∀ {A B : SepNUCStarAlgebra}, F.Hom A B → F.Hom (objOp A) (objOp B)
  /-- Units go to units. -/
  homOp_id : ∀ A : SepNUCStarAlgebra, homOp (F.idHom A) = F.idHom (objOp A)
  /-- Products go to products. -/
  homOp_comp : ∀ {A B C : SepNUCStarAlgebra} (y : F.Hom B C) (x : F.Hom A B),
    homOp (F.comp y x) = F.comp (homOp y) (homOp x)

namespace KKnEndo

variable {F : KKnFunctor} (E : KKnEndo F)

/-- A `KKn`-endofunctor preserves `KKn`-equivalence. -/
theorem kknEquivalent {A B : SepNUCStarAlgebra} (h : F.KKnEquivalent A B) :
    F.KKnEquivalent (E.objOp A) (E.objOp B) := by
  obtain ⟨x, y, hyx, hxy⟩ := h
  refine ⟨E.homOp x, E.homOp y, ?_, ?_⟩
  · rw [← E.homOp_comp y x, hyx, E.homOp_id A]
  · rw [← E.homOp_comp x y, hxy, E.homOp_id B]

/-- **Closure under a `KKn`-endofunctor** sending commutative algebras into the class. -/
theorem isKKnCommutative_of_forall
    (hE : ∀ C : SepNUCStarAlgebra, C.IsCommutative → F.IsKKnCommutative (E.objOp C))
    {A : SepNUCStarAlgebra} (hA : F.IsKKnCommutative A) : F.IsKKnCommutative (E.objOp A) := by
  obtain ⟨C, hC, hAC⟩ := hA
  exact KKnFunctor.IsKKnCommutative.of_kknEquivalent (hE C hC)
    (KKnFunctor.KKnEquivalent.symm (E.kknEquivalent hAC))

/-- **Closure under a `KKn`-endofunctor** preserving commutativity (suspension, tensoring with a
commutative algebra). -/
theorem isKKnCommutative
    (hE : ∀ C : SepNUCStarAlgebra, C.IsCommutative → (E.objOp C).IsCommutative)
    {A : SepNUCStarAlgebra} (hA : F.IsKKnCommutative A) : F.IsKKnCommutative (E.objOp A) :=
  E.isKKnCommutative_of_forall
    (fun C hC => KKnFunctor.isKKnCommutative_of_isCommutative (hE C hC)) hA

end KKnEndo

/-- **A `KKn`-bifunctor**: an object map in two variables with a functorial action on pairs of
`KKn`-classes (direct sum; minimal tensor product via the external Kasparov product). -/
structure KKnBifunctor (F : KKnFunctor) where
  /-- The object map. -/
  objOp : SepNUCStarAlgebra → SepNUCStarAlgebra → SepNUCStarAlgebra
  /-- The action on classes. -/
  homOp : ∀ {A A' B B' : SepNUCStarAlgebra},
    F.Hom A A' → F.Hom B B' → F.Hom (objOp A B) (objOp A' B')
  /-- Units go to units. -/
  homOp_id : ∀ A B : SepNUCStarAlgebra,
    homOp (F.idHom A) (F.idHom B) = F.idHom (objOp A B)
  /-- Products go to products. -/
  homOp_comp : ∀ {A A' A'' B B' B'' : SepNUCStarAlgebra} (x' : F.Hom A' A'')
    (x : F.Hom A A') (y' : F.Hom B' B'') (y : F.Hom B B'),
    homOp (F.comp x' x) (F.comp y' y) = F.comp (homOp x' y') (homOp x y)

namespace KKnBifunctor

variable {F : KKnFunctor} (P : KKnBifunctor F)

/-- A `KKn`-bifunctor preserves `KKn`-equivalence in both variables. -/
theorem kknEquivalent {A A' B B' : SepNUCStarAlgebra} (hA : F.KKnEquivalent A A')
    (hB : F.KKnEquivalent B B') : F.KKnEquivalent (P.objOp A B) (P.objOp A' B') := by
  obtain ⟨x, y, hyx, hxy⟩ := hA
  obtain ⟨u, v, hvu, huv⟩ := hB
  refine ⟨P.homOp x u, P.homOp y v, ?_, ?_⟩
  · rw [← P.homOp_comp y x v u, hyx, hvu, P.homOp_id A B]
  · rw [← P.homOp_comp x y u v, hxy, huv, P.homOp_id A' B']

/-- **Closure under a `KKn`-bifunctor** sending pairs of commutative algebras into the class. -/
theorem isKKnCommutative_of_forall
    (hP : ∀ C D : SepNUCStarAlgebra, C.IsCommutative → D.IsCommutative →
      F.IsKKnCommutative (P.objOp C D))
    {A B : SepNUCStarAlgebra} (hA : F.IsKKnCommutative A) (hB : F.IsKKnCommutative B) :
    F.IsKKnCommutative (P.objOp A B) := by
  obtain ⟨C, hC, hAC⟩ := hA
  obtain ⟨D, hD, hBD⟩ := hB
  exact KKnFunctor.IsKKnCommutative.of_kknEquivalent (hP C D hC hD)
    (KKnFunctor.KKnEquivalent.symm (P.kknEquivalent hAC hBD))

/-- **Closure under a `KKn`-bifunctor** preserving commutativity (finite direct sums, minimal
tensor products). -/
theorem isKKnCommutative
    (hP : ∀ C D : SepNUCStarAlgebra, C.IsCommutative → D.IsCommutative →
      (P.objOp C D).IsCommutative)
    {A B : SepNUCStarAlgebra} (hA : F.IsKKnCommutative A) (hB : F.IsKKnCommutative B) :
    F.IsKKnCommutative (P.objOp A B) :=
  P.isKKnCommutative_of_forall
    (fun C D hC hD => KKnFunctor.isKKnCommutative_of_isCommutative (hP C D hC hD)) hA hB

/-- **Finite iterates**: `A₁ ⊕ (A₂ ⊕ (⋯ ⊕ Z))` (or the iterated tensor product) of members of the
class is in the class. -/
theorem isKKnCommutative_foldr
    (hP : ∀ C D : SepNUCStarAlgebra, C.IsCommutative → D.IsCommutative →
      (P.objOp C D).IsCommutative)
    {Z : SepNUCStarAlgebra} (hZ : F.IsKKnCommutative Z) :
    ∀ L : List SepNUCStarAlgebra, (∀ A ∈ L, F.IsKKnCommutative A) →
      F.IsKKnCommutative (L.foldr P.objOp Z) := by
  intro L
  induction L with
  | nil =>
    intro _
    exact hZ
  | cons A L ih =>
    intro hL
    show F.IsKKnCommutative (P.objOp A (L.foldr P.objOp Z))
    exact P.isKKnCommutative hP (hL A List.mem_cons_self)
      (ih fun B hB => hL B (List.mem_cons_of_mem A hB))

end KKnBifunctor

end

end GroupApproximation.Full.TWWUCT.Bootstrap
