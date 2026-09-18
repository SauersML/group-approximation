import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureFunctorial
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapSuspension

/-!
# Suspension as a `KKn`-endofunctor

Rosenberg--Schochet (Duke Math. J. 55 (1987), §2) and Blackadar (*K-Theory for Operator
Algebras*, 19.x, 22.3.4) use that the suspension `A ↦ SA = C₀(ℝ, A)` acts on `KK`-classes
(`x ↦ x ⊗ 1_{C₀(ℝ)}`), so that the class of algebras `KK`-equivalent to commutative ones is closed
under suspension.  This file supplies that step for the UCT input of
`thm:fixed-radical-membership` in `non_mf_group_notes.tex`.

* `suspClass`: the suspension of homotopy classes, `[φ] ↦ [Sφ]`, with `suspClass_id` and
  `suspClass_comp`;
* `SuspensionStructure F`: for a `KKnFunctor` `F`, a functorial action of the suspension on
  `KKn`-classes extending `f ↦ Sf` on `⋆`-homomorphisms (for Cuntz's `F A = 𝒦 ⊗ qA` this is the
  external Kasparov product with `1_{C₀(ℝ)}`);
* `suspensionEndo F S : KKnEndo F` with `objOp := SepNUCStarAlgebra.susp`;
* the corollaries `kknEquivalent_susp`, `isKKnCommutative_susp` and
  `isKKnCommutative_susp_iterate`.
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.Full.TWWKK ZeroAtInfty

noncomputable section

section SuspClass

variable {D : Type*} {E : Type*} {G : Type*}
variable [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra G]

/-- **The suspension of a homotopy class**, `[φ] ↦ [Sφ]`. -/
def suspClass (x : HomotopyClass D E) : HomotopyClass C₀(ℝ, D) C₀(ℝ, E) :=
  Quot.lift (fun φ : D →⋆ₙₐ[ℂ] E => HomotopyClass.mk (suspMap φ))
    (fun _ _ h => HomotopyClass.mk_eq_mk_of_nHomotopic (suspMap_nHomotopic h)) x

theorem suspClass_mk (φ : D →⋆ₙₐ[ℂ] E) :
    suspClass (HomotopyClass.mk φ) = HomotopyClass.mk (suspMap φ) :=
  rfl

theorem suspClass_id : suspClass (HomotopyClass.id D) = HomotopyClass.id C₀(ℝ, D) := by
  show HomotopyClass.mk (suspMap (NonUnitalStarAlgHom.id ℂ D)) =
    HomotopyClass.mk (NonUnitalStarAlgHom.id ℂ C₀(ℝ, D))
  rw [suspMap_id]

theorem suspClass_comp (y : HomotopyClass E G) (x : HomotopyClass D E) :
    suspClass (HomotopyClass.comp y x) = HomotopyClass.comp (suspClass y) (suspClass x) := by
  induction x using HomotopyClass.ind with
  | mk φ =>
    induction y using HomotopyClass.ind with
    | mk ψ =>
      show HomotopyClass.mk (suspMap (ψ.comp φ)) =
        HomotopyClass.mk ((suspMap ψ).comp (suspMap φ))
      rw [suspMap_comp]

end SuspClass

/-- **Suspension structure** on a `KKnFunctor` `F`: a functorial action `KKn(A, B) → KKn(SA, SB)`
of the suspension on classes, sending the class of `f` to the class of `Sf`.  For Cuntz's
`F A = 𝒦 ⊗ qA` this is `x ↦ x ⊗ 1_{C₀(ℝ)}` (Kasparov's external product; Cuntz,
*A new look at KK-theory*, K-Theory 1 (1987); Blackadar 17.8, 19.x). -/
structure SuspensionStructure (F : KKnFunctor) where
  /-- The action on classes. -/
  homOp : ∀ {A B : SepNUCStarAlgebra}, F.Hom A B → F.Hom A.susp B.susp
  /-- Units go to units. -/
  homOp_id : ∀ A : SepNUCStarAlgebra, homOp (F.idHom A) = F.idHom A.susp
  /-- Products go to products. -/
  homOp_comp : ∀ {A B C : SepNUCStarAlgebra} (y : F.Hom B C) (x : F.Hom A B),
    homOp (F.comp y x) = F.comp (homOp y) (homOp x)
  /-- The action extends the suspension of `⋆`-homomorphisms. -/
  homOp_classOf : ∀ {A B : SepNUCStarAlgebra} (f : A →⋆ₙₐ[ℂ] B),
    homOp (F.classOf f) = F.classOf (A := A.susp) (B := B.susp) (suspMap f)

/-- **The suspension `KKn`-endofunctor** `A ↦ SA` of a functor with a suspension structure. -/
def suspensionEndo (F : KKnFunctor) (S : SuspensionStructure F) : KKnEndo F where
  objOp := SepNUCStarAlgebra.susp
  homOp x := S.homOp x
  homOp_id := S.homOp_id
  homOp_comp := S.homOp_comp

theorem suspensionEndo_objOp (F : KKnFunctor) (S : SuspensionStructure F)
    (A : SepNUCStarAlgebra) : (suspensionEndo F S).objOp A = A.susp :=
  rfl

section Corollaries

variable {F : KKnFunctor}

/-- **`KKn`-equivalence is compatible with suspension.** -/
theorem kknEquivalent_susp (S : SuspensionStructure F) {A B : SepNUCStarAlgebra}
    (h : F.KKnEquivalent A B) : F.KKnEquivalent A.susp B.susp :=
  (suspensionEndo F S).kknEquivalent h

/-- **Closure under suspension** (Rosenberg--Schochet 1987, §2; Blackadar 22.3.4). -/
theorem isKKnCommutative_susp (S : SuspensionStructure F) {A : SepNUCStarAlgebra}
    (hA : F.IsKKnCommutative A) : F.IsKKnCommutative A.susp :=
  (suspensionEndo F S).isKKnCommutative (fun _ hC => SepNUCStarAlgebra.IsCommutative.susp hC)
    hA

/-- **Closure under iterated suspension** `SⁿA`. -/
theorem isKKnCommutative_susp_iterate (S : SuspensionStructure F) (n : ℕ) :
    ∀ {A : SepNUCStarAlgebra}, F.IsKKnCommutative A →
      F.IsKKnCommutative (SepNUCStarAlgebra.susp^[n] A) := by
  induction n with
  | zero => exact fun hA => hA
  | succ n ih => exact fun hA => ih (isKKnCommutative_susp S hA)

end Corollaries

end

end GroupApproximation.Full.TWWUCT.Bootstrap
