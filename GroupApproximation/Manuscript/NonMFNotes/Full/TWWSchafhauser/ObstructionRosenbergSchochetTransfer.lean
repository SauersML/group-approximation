import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExt
import GroupApproximation.Analysis.UniversalCoefficientTheorem

/-!
# Transfer of "the boundary maps detect zero" along `KK`-equivalence

Lane `TWWSch3d3c`, work order `WO-TWWSchafhauser-3d3-3` (Rosenberg–Schochet injectivity half).
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, J. reine angew. Math. 759 (2020), §§4--5.

Rosenberg and Schochet prove injectivity of `Ext(S, J) → Hom(K_*S, K_{*+1}J)` in two steps
(J. Rosenberg, C. Schochet, Duke Math. J. 55 (1987), §§1--4; B. Blackadar, *K-theory for
operator algebras*, 23.1). First they treat commutative `C`. Then they move the statement
along a `KK`-equivalence `S ∼ C`, because `Ext(-, J) = KK¹(-, J)` is a module over the Kasparov
product (Blackadar 18.5, 18.7.1). This file does the second step as pure algebra.

* `ExtKKAction T P J`: a contravariant action of the Kasparov theory `T` on `Ext(-, J)`,
  restricted to objects in a class `P` (for instance, nuclear algebras), unital and compatible
  with the product;
* `ExtKKAction.PreservesNull Φ Null`: the action preserves a "boundary maps vanish" predicate;
* `ExtKKAction.detectsZero_of_kkEquivalent`: if `A ∼ C` in `T` and `Null` detects zero on
  `Ext(C, J)`, it detects zero on `Ext(A, J)`;
* `ExtKKAction.detectsZero_of_satisfiesUCT`: the same for an algebra satisfying the UCT, given
  the commutative case;
* `ExtKKAction.preservesNull_of_boundaries`: two boundary maps that are natural for the action
  give such a predicate.

Proof: for `x·y = 1_A` and `ξ` with vanishing boundaries, `η := y·ξ ∈ Ext(C, J)` has vanishing
boundaries, so `η = 0`, and then `ξ = (x·y)·ξ = x·η = 0`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.KK

section Transfer

variable (T : KasparovTheory.{0}) (P : SepCStarAlgebra.{0} → Prop)
variable (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **A contravariant action of the Kasparov theory `T` on `Ext(-, J)`**, restricted to objects
in the class `P`. A class `x ∈ KK(A, B)` gives `x^* : Ext(B, J) → Ext(A, J)`. The action is
unital and turns the Kasparov product into composition (Blackadar 18.5, 18.7.1). -/
structure ExtKKAction where
  /-- The action of `x ∈ KK(A, B)`. -/
  act : ∀ {A B : SepCStarAlgebra.{0}}, P A → P B → T.Grp A B → (ExtGroup B J →+ ExtGroup A J)
  /-- The action of a product is the composite of the actions. -/
  act_product : ∀ {A B C : SepCStarAlgebra.{0}} (hA : P A) (hB : P B) (hC : P C)
    (x : T.Grp A B) (y : T.Grp B C) (ξ : ExtGroup C J),
    act hA hC (T.product x y) ξ = act hA hB x (act hB hC y ξ)
  /-- The unit acts as the identity. -/
  act_unit : ∀ {A : SepCStarAlgebra.{0}} (hA : P A) (ξ : ExtGroup A J),
    act hA hA (T.unit A) ξ = ξ

variable {T P J}

/-- The action preserves the predicate `Null` (for example "both boundary maps vanish"). -/
def ExtKKAction.PreservesNull (Φ : ExtKKAction T P J)
    (Null : ∀ A : SepCStarAlgebra.{0}, ExtGroup A J → Prop) : Prop :=
  ∀ (A B : SepCStarAlgebra.{0}) (hA : P A) (hB : P B) (x : T.Grp A B) (ξ : ExtGroup B J),
    Null B ξ → Null A (Φ.act hA hB x ξ)

/-- `Null` **detects zero** on `Ext(A, J)`: only the zero class satisfies it. -/
def ExtGroup.DetectsZero (Null : ∀ A : SepCStarAlgebra.{0}, ExtGroup A J → Prop)
    (A : SepCStarAlgebra.{0}) : Prop :=
  ∀ ξ : ExtGroup A J, Null A ξ → ξ = 0

/-- **Transfer along a `KK`-equivalence.** If `A ∼ C` in `T` and `Null` detects zero on
`Ext(C, J)`, then it detects zero on `Ext(A, J)`. -/
theorem ExtKKAction.detectsZero_of_kkEquivalent (Φ : ExtKKAction T P J)
    {Null : ∀ A : SepCStarAlgebra.{0}, ExtGroup A J → Prop} (hnull : Φ.PreservesNull Null)
    {A C : SepCStarAlgebra.{0}} (hA : P A) (hC : P C) (hAC : T.KKEquivalent A C)
    (hdet : ExtGroup.DetectsZero Null C) : ExtGroup.DetectsZero Null A := by
  obtain ⟨x, y, hxy, _⟩ := hAC
  intro ξ hξ
  have hη : Φ.act hC hA y ξ = 0 := hdet (Φ.act hC hA y ξ) (hnull C A hC hA y ξ hξ)
  calc ξ = Φ.act hA hA (T.unit A) ξ := (Φ.act_unit hA ξ).symm
    _ = Φ.act hA hA (T.product x y) ξ := by rw [hxy]
    _ = Φ.act hA hC x (Φ.act hC hA y ξ) := Φ.act_product hA hC hA x y ξ
    _ = 0 := by rw [hη, map_zero]

/-- **Transfer to UCT algebras.** If `Null` detects zero on `Ext(C, J)` for every commutative
`C` in the class `P`, then it does so for every `S ∈ P` satisfying the UCT for `T`. -/
theorem ExtKKAction.detectsZero_of_satisfiesUCT (Φ : ExtKKAction T P J)
    {Null : ∀ A : SepCStarAlgebra.{0}, ExtGroup A J → Prop} (hnull : Φ.PreservesNull Null)
    (hcomm : ∀ C : SepCStarAlgebra.{0}, C.IsCommutative → P C ∧ ExtGroup.DetectsZero Null C)
    {S : SepCStarAlgebra.{0}} (hS : P S) (hUCT : T.SatisfiesUCT S) :
    ExtGroup.DetectsZero Null S := by
  obtain ⟨C, hCcomm, hSC⟩ := hUCT
  obtain ⟨hC, hdet⟩ := hcomm C hCcomm
  exact Φ.detectsZero_of_kkEquivalent hnull hS hC hSC hdet

/-- **Boundary maps natural for the action preserve vanishing.** If `β₀, β₁` intertwine the
action with additive maps `ω₀, ω₁` on their targets, then "`β₀ ξ = 0` and `β₁ ξ = 0`" is
preserved. -/
theorem ExtKKAction.preservesNull_of_boundaries (Φ : ExtKKAction T P J)
    {Obs₀ Obs₁ : SepCStarAlgebra.{0} → Type} [∀ A, AddCommGroup (Obs₀ A)]
    [∀ A, AddCommGroup (Obs₁ A)]
    (β₀ : ∀ A : SepCStarAlgebra.{0}, ExtGroup A J →+ Obs₀ A)
    (β₁ : ∀ A : SepCStarAlgebra.{0}, ExtGroup A J →+ Obs₁ A)
    (ω₀ : ∀ {A B : SepCStarAlgebra.{0}}, P A → P B → T.Grp A B → (Obs₀ B →+ Obs₀ A))
    (ω₁ : ∀ {A B : SepCStarAlgebra.{0}}, P A → P B → T.Grp A B → (Obs₁ B →+ Obs₁ A))
    (nat₀ : ∀ {A B : SepCStarAlgebra.{0}} (hA : P A) (hB : P B) (x : T.Grp A B)
      (ξ : ExtGroup B J), β₀ A (Φ.act hA hB x ξ) = ω₀ hA hB x (β₀ B ξ))
    (nat₁ : ∀ {A B : SepCStarAlgebra.{0}} (hA : P A) (hB : P B) (x : T.Grp A B)
      (ξ : ExtGroup B J), β₁ A (Φ.act hA hB x ξ) = ω₁ hA hB x (β₁ B ξ)) :
    Φ.PreservesNull (fun A ξ => β₀ A ξ = 0 ∧ β₁ A ξ = 0) := by
  intro A B hA hB x ξ hξ
  have h0 : β₀ B ξ = 0 := hξ.1
  have h1 : β₁ B ξ = 0 := hξ.2
  refine ⟨?_, ?_⟩
  · show β₀ A (Φ.act hA hB x ξ) = 0
    rw [nat₀ hA hB x ξ, h0, map_zero]
  · show β₁ A (Φ.act hA hB x ξ) = 0
    rw [nat₁ hA hB x ξ, h1, map_zero]

end Transfer

end GroupApproximation.Full.TWWSchafhauser
