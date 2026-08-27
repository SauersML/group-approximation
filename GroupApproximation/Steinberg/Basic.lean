import Mathlib.GroupTheory.PresentedGroup
import Mathlib.SetTheory.Cardinal.Free
import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.Sofic.CentralCoverInheritance

/-!
# Steinberg groups and the canonical elementary projection

This file introduces the actual Steinberg presentation over an associative
unital ring.  It is intentionally limited to the algebraic presentation and
the canonical surjection onto the elementary matrix group.  The classical
Kervaire--Steinberg theorem that this projection is a universal central
extension in rank at least five is a deeper, separate input.
-/

namespace GroupApproximation

open scoped commutatorElement

/-- A Steinberg generator `xᵢⱼ(a)`, including the off-diagonal condition. -/
structure SteinbergGenerator (I R : Type*) where
  row : I
  column : I
  row_ne_column : row ≠ column
  coefficient : R

noncomputable instance SteinbergGenerator.instCountable
    (I R : Type*) [Countable I] [Countable R] :
    Countable (SteinbergGenerator I R) := by
  apply (show Function.Injective
      (fun g : SteinbergGenerator I R ↦ (g.row, g.column, g.coefficient)) from ?_).countable
  intro x y h
  cases x
  cases y
  simp_all

namespace SteinbergGroup

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

private def generator (i j : I) (hij : i ≠ j) (a : R) :
    SteinbergGenerator I R :=
  ⟨i, j, hij, a⟩

/-- The three families of Steinberg relators. -/
inductive IsRelation : FreeGroup (SteinbergGenerator I R) → Prop
  | add (i j : I) (hij : i ≠ j) (a b : R) :
      IsRelation
        (FreeGroup.of (generator i j hij a) *
          FreeGroup.of (generator i j hij b) *
          (FreeGroup.of (generator i j hij (a + b)))⁻¹)
  | commute (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
      (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
      IsRelation
        ⁅FreeGroup.of (generator i j hij a),
          FreeGroup.of (generator k l hkl b)⁆
  | adjacent (i j k : I) (hij : i ≠ j) (hjk : j ≠ k)
      (hik : i ≠ k) (a b : R) :
      IsRelation
        (⁅FreeGroup.of (generator i j hij a),
            FreeGroup.of (generator j k hjk b)⁆ *
          (FreeGroup.of (generator i k hik (a * b)))⁻¹)

/-- The relator set defining the Steinberg group. -/
def relations : Set (FreeGroup (SteinbergGenerator I R)) :=
  {w | IsRelation w}

/-- The word expressing additivity in a Steinberg root subgroup. -/
def addRelationWord (i j : I) (hij : i ≠ j) (a b : R) :
    FreeGroup (SteinbergGenerator I R) :=
  FreeGroup.of (generator i j hij a) *
    FreeGroup.of (generator i j hij b) *
    (FreeGroup.of (generator i j hij (a + b)))⁻¹

end SteinbergGroup

/-- The Steinberg group `St_I(R)`. -/
abbrev SteinbergGroup (I R : Type*) [Fintype I] [DecidableEq I] [Ring R] :=
  PresentedGroup (SteinbergGroup.relations (I := I) (R := R))

noncomputable instance SteinbergGroup.instCountable
    (I R : Type*) [Fintype I] [DecidableEq I] [Ring R] [Countable R] :
    Countable (SteinbergGroup I R) :=
  (PresentedGroup.mk_surjective
    (SteinbergGroup.relations (I := I) (R := R))).countable

namespace SteinbergGroup

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- The canonical generator `xᵢⱼ(a)` in the Steinberg group. -/
def x (i j : I) (hij : i ≠ j) (a : R) : SteinbergGroup (I := I) (R := R) :=
  PresentedGroup.of (generator i j hij a)

/-- Additivity of each Steinberg root subgroup. -/
theorem x_mul (i j : I) (hij : i ≠ j) (a b : R) :
    x i j hij a * x i j hij b = x i j hij (a + b) := by
  apply eq_of_mul_inv_eq_one
  have hrel :
      FreeGroup.of (generator i j hij a) *
          FreeGroup.of (generator i j hij b) *
          (FreeGroup.of (generator i j hij (a + b)))⁻¹ ∈
        relations (I := I) (R := R) :=
    IsRelation.add i j hij a b
  simpa only [x, PresentedGroup.of, map_mul, map_inv] using
    (PresentedGroup.one_of_mem hrel)

@[simp] theorem x_zero (i j : I) (hij : i ≠ j) :
    x (R := R) i j hij 0 = 1 := by
  have h := x_mul (R := R) i j hij 0 0
  rw [zero_add] at h
  apply mul_left_cancel (a := x (R := R) i j hij 0)
  simpa only [mul_one] using h

@[simp] theorem x_neg (i j : I) (hij : i ≠ j) (a : R) :
    x i j hij (-a) = (x i j hij a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [x_mul]
  simp

/-- Non-addable Steinberg roots commute. -/
theorem x_commute_of_ne
    (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    Commute (x i j hij a) (x k l hkl b) := by
  rw [commute_iff_eq]
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hrel :
      ⁅FreeGroup.of (generator i j hij a),
          FreeGroup.of (generator k l hkl b)⁆ ∈
        relations (I := I) (R := R) :=
    IsRelation.commute i j k l hij hkl hjk hli a b
  simpa only [x, PresentedGroup.of, map_commutatorElement] using
    (PresentedGroup.one_of_mem hrel)

/-- The adjacent-root Steinberg commutator relation. -/
theorem x_commutator (i j k : I)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅x i j hij a, x j k hjk b⁆ = x i k hik (a * b) := by
  apply eq_of_mul_inv_eq_one
  have hrel :
      ⁅FreeGroup.of (generator i j hij a),
          FreeGroup.of (generator j k hjk b)⁆ *
          (FreeGroup.of (generator i k hik (a * b)))⁻¹ ∈
        relations (I := I) (R := R) :=
    IsRelation.adjacent i j k hij hjk hik a b
  simpa only [x, PresentedGroup.of, map_mul, map_inv,
      map_commutatorElement] using
    (PresentedGroup.one_of_mem hrel)

/-- Interpret a Steinberg generator as its elementary matrix. -/
def generatorImage (g : SteinbergGenerator I R) : elementaryGroup I R :=
  elementaryRoot g.row g.column g.row_ne_column g.coefficient

private theorem generatorImage_kills_relations
    (w : FreeGroup (SteinbergGenerator I R))
    (hw : w ∈ relations (I := I) (R := R)) :
    FreeGroup.lift generatorImage w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, generatorImage, generator]
      rw [elementaryRoot_mul]
      simp
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅elementaryRoot i j hij a, elementaryRoot k l hkl b⁆ = 1
      exact (elementaryRoot_commute_of_ne i j k l hij hkl hjk hli a b).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        generatorImage, generator]
      rw [elementaryRoot_commutator i j k hij hjk hik]
      simp

/-- The canonical homomorphism `St_I(R) → EL_I(R)`. -/
def projection : SteinbergGroup (I := I) (R := R) →* elementaryGroup I R :=
  PresentedGroup.toGroup (f := generatorImage) generatorImage_kills_relations

@[simp] theorem projection_x (i j : I) (hij : i ≠ j) (a : R) :
    projection (x i j hij a) = elementaryRoot i j hij a := by
  simp [projection, x, generatorImage, generator]

/-- Each Steinberg root parametrization is injective.  This follows from
the canonical projection, because elementary transvections remember their
off-diagonal coefficient. -/
theorem x_injective (i j : I) (hij : i ≠ j) :
    Function.Injective (x (R := R) i j hij) := by
  intro a b hab
  have hp := congrArg (projection (I := I) (R := R)) hab
  rw [projection_x, projection_x] at hp
  exact elementaryUnit_injective i j hij
    (congrArg Subtype.val hp)

/-- The canonical Steinberg projection is onto the elementary group. -/
theorem projection_surjective :
    Function.Surjective (projection (I := I) (R := R)) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← elementaryRootSet_generate (I := I) (R := R)]
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨i, j, hij, a, rfl⟩ := hg
  exact ⟨x i j hij a, projection_x i j hij a⟩

/-- Once centrality of its kernel is supplied, the canonical Steinberg
projection is a `CentralExtension` in the exact interface used by the
quotient-rigidity development. -/
def centralExtension
    (hker : (projection (I := I) (R := R)).ker ≤
      Subgroup.center (SteinbergGroup (I := I) (R := R))) :
    CentralExtension (SteinbergGroup (I := I) (R := R))
      (elementaryGroup I R) where
  projection := projection
  surjective := projection_surjective
  ker_le_center := hker

end SteinbergGroup
end GroupApproximation
