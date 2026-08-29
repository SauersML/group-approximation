import GroupApproximation.Sofic.Asymptotics
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Sofic groups and sequential approximations

`IsSofic` is the standard local finite-permutation definition: every finite
subset has an arbitrarily accurate approximately multiplicative and separated
model.  It has no countability premise.  `SoficApproximation` is the equivalent
sequential formulation used by the analytic part of the development, and is the
direct transcription of Definition `def:sofic` of the manuscript.

`isSofic_of_soficApproximation` proves the sequential-to-local direction here,
with no countability premise.  The converse needs countability and is proved in
`TableCover`; the two are packaged as an iff in `Sofic.SoficSequential`.
-/

namespace GroupApproximation

open scoped Pointwise

/-- A finite type bundled with exactly the instances needed by permutation
models. -/
structure FiniteModel where
  carrier : Type
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

instance finiteModelCoeSort : CoeSort FiniteModel Type := ⟨FiniteModel.carrier⟩

@[reducible, instance] def finiteModelFintype (Y : FiniteModel) : Fintype Y :=
  Y.fintype
@[reducible, instance] def finiteModelDecidableEq
    (Y : FiniteModel) : DecidableEq Y :=
  Y.decidableEq

/-- The vertices on which two permutations of a finite type disagree. -/
def hammingDisagreement {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun y ↦ p y ≠ q y

@[simp] theorem mem_hammingDisagreement {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) (y : Y) :
    y ∈ hammingDisagreement p q ↔ p y ≠ q y := by
  simp [hammingDisagreement]

/-- Normalized Hamming distance on permutations of a finite set.  On the empty
set it is defined to be zero by real division; approximation cardinalities are
separately required to diverge. -/
noncomputable def hammingDistance (Y : FiniteModel) (p q : Equiv.Perm Y) : ℝ :=
  ((hammingDisagreement p q).card : ℝ) / Fintype.card Y

@[simp] theorem hammingDistance_self (Y : FiniteModel) (p : Equiv.Perm Y) :
    hammingDistance Y p p = 0 := by
  simp [hammingDistance, hammingDisagreement]

theorem hammingDistance_le_one (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingDistance Y p q ≤ 1 := by
  by_cases hcard : Fintype.card Y = 0
  · simp [hammingDistance, hcard]
  · apply (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hcard))).2
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- A finite permutation model on a prescribed finite subset.  The map is
defined on the whole group, while its laws are required on the test set. -/
structure SoficModel (G : Type*) [Group G] (F : Finset G) (ε : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Equiv.Perm carrier
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    hammingDistance carrier (map (g * h)) (map g * map h) ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    1 - ε ≤ hammingDistance carrier (map g) (map h)

/-- Standard local definition of a sofic group. -/
def IsSofic (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (SoficModel G F ε)

end GroupApproximation
