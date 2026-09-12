/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Bowen–Chapman Problem 1.1: a surjunctive group that is not sofic

L. Bowen and M. Chapman, *Surjunctivity does not characterize cosoficity of
invariant random subgroups* (arXiv:2511.06586), print as Problem 1.1, verbatim:

> Are all surjunctive groups sofic? Namely, does surjunctivity characterize
> soficity?

A group is surjunctive when every injective cellular automaton over it, with a
finite palette, is surjective.  Gromov and Weiss proved that every sofic group
is surjunctive; Problem 1.1 asks for the converse.  Bowen and Chapman pose it for
a finitely generated group and a finite set of colours.

The two theorems below answer **no**:

* `exists_finitelyGenerated_surjunctive_not_sofic` is the negative answer in
  that setting: a finitely generated group that is surjunctive and not sofic;
* `not_all_surjunctive_groups_sofic` states the negation without the finite
  generation.

## Vocabulary

Every notion except the definitions in the shared block is Mathlib's.

* `cellularAutomaton γ φ` is Bowen–Chapman's cellular automaton with memory
  `γ₁, …, γₙ` and local rule `φ`, the map `Φ(c)(x) = φ(c(x γ₁), …, c(x γₙ))`
  on colourings `c : G → A`.
* `IsSurjunctive G`: every injective cellular automaton on `G` over a finite
  palette is surjective.  Palettes range over the finite types in `Type`.
* `IsSoficGroup G` is soficity in the finite-set normalized-Hamming form: for
  every finite `F ⊆ G` and `ε > 0` there is a map from `G` to the permutations
  of a nonempty finite set that is `ε`-multiplicative on `F` and separates any
  two distinct elements of `F` by normalized Hamming distance at least `1 - ε`.
* Finite generation is the existence of a finite subset whose generated
  subgroup is the whole group.

All groups are quantified over `Type`, where the counterexample lives.
-/

namespace BowenChapman

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/BowenChapmanChallenge.lean` and `Palomar/BowenChapmanSolution.lean`)

/-- A cellular automaton on `G` with palette `A`, in Bowen–Chapman's form
`Φ(c)(x) = φ(c(x γ₁), …, c(x γₙ))`. -/
def cellularAutomaton {G : Type} [Group G] {A : Type} {n : ℕ}
    (γ : Fin n → G) (φ : (Fin n → A) → A) : (G → A) → (G → A) :=
  fun c x => φ fun i => c (x * γ i)

/-- Surjunctivity: every injective cellular automaton on `G` over a finite
palette is surjective. -/
def IsSurjunctive (G : Type) [Group G] : Prop :=
  ∀ (A : Type) [Finite A] (n : ℕ) (γ : Fin n → G) (φ : (Fin n → A) → A),
    Function.Injective (cellularAutomaton γ φ) → Function.Surjective (cellularAutomaton γ φ)

/-- A finite index type for permutation models. -/
structure FiniteCarrier where
  carrier : Type
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

instance finiteCarrierCoeSort : CoeSort FiniteCarrier Type :=
  ⟨FiniteCarrier.carrier⟩

@[reducible, instance] def finiteCarrierFintype (Y : FiniteCarrier) :
    Fintype Y :=
  Y.fintype

@[reducible, instance] def finiteCarrierDecidableEq (Y : FiniteCarrier) :
    DecidableEq Y :=
  Y.decidableEq

/-- The proportion of points where two finite permutations differ. -/
def hammingDist (Y : FiniteCarrier) (p q : Equiv.Perm Y) : ℝ :=
  ((Finset.univ.filter fun y : Y ↦ p y ≠ q y).card : ℝ) / Fintype.card Y

/-- Soficity in the finite-set normalized-Hamming formulation. -/
def IsSoficGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (σ : G → Equiv.Perm Y),
      0 < Fintype.card Y ∧
      (∀ g ∈ F, ∀ h ∈ F, hammingDist Y (σ (g * h)) (σ g * σ h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 1 - ε ≤ hammingDist Y (σ g) (σ h))

-- END SHARED BLOCK

/-- **Problem 1.1 has a negative answer**: not every surjunctive group is
sofic. -/
theorem not_all_surjunctive_groups_sofic :
    ¬ ∀ (G : Type) [Group G], IsSurjunctive G → IsSoficGroup G := by
  sorry

/-- **A finitely generated counterexample**: some finitely generated group is
surjunctive and not sofic. -/
theorem exists_finitelyGenerated_surjunctive_not_sofic :
    ∃ (G : Type) (_ : Group G), (∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤) ∧
      IsSurjunctive G ∧ ¬ IsSoficGroup G := by
  sorry

end

end BowenChapman
