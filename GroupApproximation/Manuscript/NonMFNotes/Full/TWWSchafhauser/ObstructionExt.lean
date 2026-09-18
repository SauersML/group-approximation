import GroupApproximation.Analysis.CStarStandardModuleEquiv
import GroupApproximation.Analysis.CStarCompactOperators
import GroupApproximation.Analysis.KasparovBimodule
import GroupApproximation.Analysis.KKTheoryKasparov
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# The extension group `Ext(S, J) = KK¹(S, J)` in the Busby picture

Lane `TWWSchafhauser-3d2`, work order `WO-TWWSchafhauser-3d-2(a)`.

Schafhauser's proof of the Tikuisis–White–Winter theorem (C. Schafhauser, *A new proof of the
Tikuisis–White–Winter theorem*, J. reine angew. Math. 759 (2020), §§4–5) uses the obstruction
class of an extension `0 → J → E → S → 0` in `KK¹(S, J)`. For separable nuclear `S` and σ-unital
`J`, `KK¹(S, J)` is the group `Ext(S, J)` of extensions modulo split extensions (G. G. Kasparov,
*The operator K-functor and extensions of C⋆-algebras*, Izv. Akad. Nauk SSSR 44 (1980); the
Choi–Effros lifting theorem makes every extension semisplit). This is the picture used here.

An extension is recorded by its **Busby map** `S → Q(J ⊗ 𝒦) = 𝓛(H_J)/𝒦(H_J)`, with
`H_J = standardModule ℕ J`. We present a Busby map by a pointwise lift into the adjointable
operators on `H_J` that is additive, linear, multiplicative and `⋆`-preserving *modulo compact
operators* (`BusbyCycle`). This avoids forming the corona algebra as a quotient type.

`ExtGroup S J` is the free abelian group on cycles modulo three families of relations:

* split cycles (those that agree modulo compacts with an honest representation) are `0`;
* unitarily equivalent cycles are equal, with compact perturbation as the case `U = 1`;
* a cycle that is unitarily equivalent to the direct sum `x ⊕ y` equals `x + y`.

The quotient is abelian by construction. On the Kasparov side, where the semigroup of classes is
already a group, the presented group is canonically isomorphic to the Grothendieck group of that
group, i.e. to `Ext(S, J)` itself.

* `ExtGroup.mk_eq_zero_of_isSplit`, `ExtGroup.mk_eq_of_isUnitarilyEquivalent`,
  `ExtGroup.mk_eq_add_of_isDirectSum`: the relations hold.
* `ExtGroup.lift`, `ExtGroup.lift_mk`, `ExtGroup.hom_ext`: the universal property.
* `KKOne S J`: the `KK¹` notation for separable `S`.

The extension class `extClass` is in `ObstructionExtClass`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Cycles

variable (S : Type) [NonUnitalCStarAlgebra S]
variable (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The adjointable operators on the standard module `H_J = ℓ²(ℕ, J)`, i.e. the multiplier
algebra of `J ⊗ 𝒦`. -/
abbrev StdOp : Type :=
  Adjointable (standardModule ℕ J) (standardModule ℕ J)

/-- Two operators on `H_J` have the same image in the corona algebra `Q(J ⊗ 𝒦)`. -/
def CompactEq (T T' : StdOp J) : Prop :=
  Adjointable.IsCompactOp (Adjointable.sub T T')

/-- A **Busby cycle**: a set-theoretic lift `S → 𝓛(H_J)` of a `⋆`-homomorphism
`S → 𝓛(H_J)/𝒦(H_J)`. Every clause holds modulo compact operators. -/
structure BusbyCycle : Type where
  /-- The lift of the Busby map. -/
  lift : S → StdOp J
  /-- Each lifted element is bounded. -/
  bounded : ∀ a : S, Adjointable.IsBounded (lift a)
  /-- Additive modulo compacts. -/
  map_add : ∀ a a' : S, CompactEq J (lift (a + a')) (Adjointable.add (lift a) (lift a'))
  /-- Linear modulo compacts. -/
  map_smul : ∀ (c : ℂ) (a : S), CompactEq J (lift (c • a)) (Adjointable.smul c (lift a))
  /-- Multiplicative modulo compacts. -/
  map_mul : ∀ a a' : S, CompactEq J (lift (a * a')) (Adjointable.comp (lift a) (lift a'))
  /-- `⋆`-preserving modulo compacts. -/
  map_star : ∀ a : S, CompactEq J (lift (star a)) (Adjointable.adjoint (lift a))

variable {S J}

/-- A cycle is **split** when it agrees modulo compacts with an honest representation of `S`
on `H_J`, i.e. the Busby map lifts to a `⋆`-homomorphism `S → 𝓛(H_J)`. -/
def BusbyCycle.IsSplit (x : BusbyCycle S J) : Prop :=
  ∃ ρ : S → StdOp J, IsRepresentation (standardModule ℕ J) ρ ∧
    ∀ a : S, CompactEq J (x.lift a) (ρ a)

/-- Two cycles are **unitarily equivalent**: `Ad U ∘ x = y` in the corona algebra. -/
def BusbyCycle.IsUnitarilyEquivalent (x y : BusbyCycle S J) : Prop :=
  ∃ U : StdOp J, Adjointable.IsUnitaryAdj U ∧
    ∀ a : S, CompactEq J
      (Adjointable.comp U (Adjointable.comp (x.lift a) (Adjointable.adjoint U))) (y.lift a)

/-- `z` is the **direct sum** of `x` and `y`: under a unitary `H_J ⊕ H_J ≅ H_J`, the diagonal
`x ⊕ y` agrees with `z` modulo compacts. -/
def BusbyCycle.IsDirectSum (z x y : BusbyCycle S J) : Prop :=
  ∃ U : Adjointable (prod (standardModule ℕ J) (standardModule ℕ J)) (standardModule ℕ J),
    Adjointable.IsUnitaryAdj U ∧
    ∀ a : S, CompactEq J
      (Adjointable.comp U (Adjointable.comp (Adjointable.prodMap (x.lift a) (y.lift a))
        (Adjointable.adjoint U))) (z.lift a)

variable (S J)

/-- The generating relations of `Ext(S, J)`. -/
def extGenerators : Set (FreeAbelianGroup (BusbyCycle S J)) :=
  {r | (∃ x : BusbyCycle S J, x.IsSplit ∧ r = FreeAbelianGroup.of x) ∨
    (∃ x y : BusbyCycle S J, x.IsUnitarilyEquivalent y ∧
      r = FreeAbelianGroup.of x - FreeAbelianGroup.of y) ∨
    (∃ z x y : BusbyCycle S J, z.IsDirectSum x y ∧
      r = FreeAbelianGroup.of z - (FreeAbelianGroup.of x + FreeAbelianGroup.of y))}

/-- The subgroup generated by the relations. -/
def extRelations : AddSubgroup (FreeAbelianGroup (BusbyCycle S J)) :=
  AddSubgroup.closure (extGenerators S J)

/-- **`Ext(S, J)`**: Busby cycles modulo split cycles, unitary equivalence and direct sums. -/
abbrev ExtGroup : Type :=
  FreeAbelianGroup (BusbyCycle S J) ⧸ extRelations S J

variable {S J}

/-- The class of a Busby cycle. -/
def ExtGroup.mk (x : BusbyCycle S J) : ExtGroup S J :=
  ((FreeAbelianGroup.of x : FreeAbelianGroup (BusbyCycle S J)) : ExtGroup S J)

/-- A split cycle has class `0`. -/
theorem ExtGroup.mk_eq_zero_of_isSplit {x : BusbyCycle S J} (hx : x.IsSplit) :
    ExtGroup.mk x = 0 := by
  show ((FreeAbelianGroup.of x : FreeAbelianGroup (BusbyCycle S J)) : ExtGroup S J) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure
    (show FreeAbelianGroup.of x ∈ extGenerators S J from Or.inl ⟨x, hx, rfl⟩)

/-- Unitarily equivalent cycles have the same class. -/
theorem ExtGroup.mk_eq_of_isUnitarilyEquivalent {x y : BusbyCycle S J}
    (h : x.IsUnitarilyEquivalent y) : ExtGroup.mk x = ExtGroup.mk y := by
  show ((FreeAbelianGroup.of x : FreeAbelianGroup (BusbyCycle S J)) : ExtGroup S J) =
    ((FreeAbelianGroup.of y : FreeAbelianGroup (BusbyCycle S J)) : ExtGroup S J)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure
    (show FreeAbelianGroup.of x - FreeAbelianGroup.of y ∈ extGenerators S J from
      Or.inr (Or.inl ⟨x, y, h, rfl⟩))

/-- The class of a direct sum is the sum of the classes. -/
theorem ExtGroup.mk_eq_add_of_isDirectSum {z x y : BusbyCycle S J} (h : z.IsDirectSum x y) :
    ExtGroup.mk z = ExtGroup.mk x + ExtGroup.mk y := by
  show ((FreeAbelianGroup.of z : FreeAbelianGroup (BusbyCycle S J)) : ExtGroup S J) =
    ((FreeAbelianGroup.of x : FreeAbelianGroup (BusbyCycle S J)) : ExtGroup S J) +
      ((FreeAbelianGroup.of y : FreeAbelianGroup (BusbyCycle S J)) : ExtGroup S J)
  rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure
    (show FreeAbelianGroup.of z - (FreeAbelianGroup.of x + FreeAbelianGroup.of y) ∈
      extGenerators S J from Or.inr (Or.inr ⟨z, x, y, h, rfl⟩))

variable (S J)

/-- An assignment of values to cycles that respects the defining relations of `Ext(S, J)`. -/
structure ExtGroup.Respecting (G : Type*) [AddCommGroup G] where
  /-- The value on a cycle. -/
  toFun : BusbyCycle S J → G
  /-- Split cycles go to `0`. -/
  map_split : ∀ x : BusbyCycle S J, x.IsSplit → toFun x = 0
  /-- Unitarily equivalent cycles have equal values. -/
  map_unitary : ∀ x y : BusbyCycle S J, x.IsUnitarilyEquivalent y → toFun x = toFun y
  /-- Direct sums are additive. -/
  map_sum : ∀ z x y : BusbyCycle S J, z.IsDirectSum x y → toFun z = toFun x + toFun y

variable {S J}

theorem ExtGroup.extRelations_le_ker {G : Type*} [AddCommGroup G] (f : ExtGroup.Respecting S J G) :
    extRelations S J ≤ (FreeAbelianGroup.lift f.toFun).ker := by
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro r (⟨x, hx, rfl⟩ | ⟨x, y, h, rfl⟩ | ⟨z, x, y, h, rfl⟩)
  · refine AddMonoidHom.mem_ker.mpr ?_
    rw [FreeAbelianGroup.lift_apply_of]
    exact f.map_split x hx
  · refine AddMonoidHom.mem_ker.mpr ?_
    rw [map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      f.map_unitary x y h, sub_self]
  · refine AddMonoidHom.mem_ker.mpr ?_
    rw [map_sub, map_add, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, f.map_sum z x y h, sub_self]

/-- **The universal property of `Ext(S, J)`**: a relation-respecting assignment induces a
homomorphism. -/
def ExtGroup.lift {G : Type*} [AddCommGroup G] (f : ExtGroup.Respecting S J G) :
    ExtGroup S J →+ G :=
  QuotientAddGroup.lift (extRelations S J) (FreeAbelianGroup.lift f.toFun)
    (ExtGroup.extRelations_le_ker f)

theorem ExtGroup.lift_mk {G : Type*} [AddCommGroup G] (f : ExtGroup.Respecting S J G)
    (x : BusbyCycle S J) : ExtGroup.lift f (ExtGroup.mk x) = f.toFun x := by
  show FreeAbelianGroup.lift f.toFun (FreeAbelianGroup.of x) = f.toFun x
  exact FreeAbelianGroup.lift_apply_of f.toFun x

/-- Homomorphisms out of `Ext(S, J)` are determined by their values on cycles. -/
theorem ExtGroup.hom_ext {G : Type*} [AddCommGroup G] {φ ψ : ExtGroup S J →+ G}
    (h : ∀ x : BusbyCycle S J, φ (ExtGroup.mk x) = ψ (ExtGroup.mk x)) : φ = ψ :=
  QuotientAddGroup.addMonoidHom_ext _
    (FreeAbelianGroup.lift_ext _ _ fun x => h x)

/-- Every class is an integer combination of cycle classes: induction principle. -/
theorem ExtGroup.induction_on {P : ExtGroup S J → Prop} (ξ : ExtGroup S J)
    (zero : P 0) (mk : ∀ x : BusbyCycle S J, P (ExtGroup.mk x))
    (neg : ∀ x : BusbyCycle S J, P (-ExtGroup.mk x))
    (add : ∀ ξ η : ExtGroup S J, P ξ → P η → P (ξ + η)) : P ξ := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective (extRelations S J) ξ
  exact FreeAbelianGroup.induction_on
    (motive := fun g => P (QuotientAddGroup.mk' (extRelations S J) g)) g zero
    (fun x => mk x) (fun x _ => neg x) (fun g g' hg hg' => add _ _ hg hg')

end Cycles

/-- **`KK¹(S, J)`** for a separable C⋆-algebra `S`, in the Busby picture. For nuclear `S` and
σ-unital `J` this is Kasparov's `KK¹(S, J) = Ext(S, J)`. -/
abbrev KKOne (S : KK.SepCStarAlgebra.{0}) (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J]
    [StarOrderedRing J] : Type :=
  ExtGroup S J

end GroupApproximation.Full.TWWSchafhauser
