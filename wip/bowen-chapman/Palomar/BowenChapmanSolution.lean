/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import GroupApproximation.Sofic.Sofic
import GroupApproximation.Dynamics.Surjunctivity

/-!
# Proof of the Bowen–Chapman Problem 1.1 theorems

This file repeats the challenge's shared block byte for byte and translates the
development's vocabulary into it.

* `isSoficGroup_of_isSofic` and `isSofic_of_isSoficGroup`: the challenge's
  `IsSoficGroup` is the development's `GroupApproximation.IsSofic`, with the
  model carrier repackaged.
* `isSurjunctive_of_surjunctive`: the development's
  `GroupApproximation.Surjunctivity.IsSurjunctive` (every injective continuous
  shift-equivariant map of a finite full shift is surjective) gives the
  challenge's `IsSurjunctive`, because Bowen–Chapman's automaton with memory
  `γ` is the development's `localMap` whose memory set is the image of `γ`.
* `closure_eq_top_of_fg`: `Group.FG` gives a finite generating set.

## What this file still owes

The development endpoint `GroupApproximation.BowenChapman.exists_fg_surjunctive_not_isSofic`,
a finitely generated group that is surjunctive in the development's sense and
not sofic, is not in this file's import closure yet.  So each theorem
`Palomar/comparator-bowen-chapman.json` selects appears here in its `_of` form,
with that endpoint statement as its one hypothesis, and every other step is
proved.  When the endpoint lands, the two unsuffixed theorems are one-line
applications of these, and the configuration moves from
`PALOMAR_PENDING_CONFIGS` to `PALOMAR_CONFIGS` in
`scripts/check_palomar_submission.py`.
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

open GroupApproximation

/-- The development's soficity gives the challenge's. -/
theorem isSoficGroup_of_isSofic {G : Type} [Group G] (h : IsSofic G) :
    IsSoficGroup G := by
  intro F ε hε
  obtain ⟨m⟩ := h F ε hε
  exact ⟨⟨m.carrier.carrier, m.carrier.fintype, m.carrier.decidableEq⟩,
    m.map, m.nonempty, m.multiplicative, m.separated⟩

/-- The challenge's soficity gives the development's. -/
theorem isSofic_of_isSoficGroup {G : Type} [Group G] (h : IsSoficGroup G) :
    IsSofic G := by
  intro F ε hε
  obtain ⟨Y, σ, hY, hmul, hsep⟩ := h F ε hε
  exact ⟨{ carrier := ⟨Y.carrier, Y.fintype, Y.decidableEq⟩
           nonempty := hY
           map := σ
           multiplicative := hmul
           separated := hsep }⟩

/-- The two soficity notions agree. -/
theorem isSoficGroup_iff_isSofic {G : Type} [Group G] :
    IsSoficGroup G ↔ IsSofic G :=
  ⟨isSofic_of_isSoficGroup, isSoficGroup_of_isSofic⟩

/-- The development's surjunctivity gives the challenge's: Bowen–Chapman's
automaton with memory `γ` and rule `φ` is the development's `localMap` whose
memory set is the image of `γ`, read through `φ`.  The palette is given its
discrete topology and the `Fintype` structure of a finite type. -/
theorem isSurjunctive_of_surjunctive {G : Type} [Group G]
    (h : Surjunctivity.IsSurjunctive G) : IsSurjunctive G := by
  intro A _ n γ φ hinj
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  let M : Finset G := Finset.univ.image γ
  let μ : (M → A) → A := fun y =>
    φ fun i => y ⟨γ i, Finset.mem_image_of_mem γ (Finset.mem_univ i)⟩
  have hloc : Surjunctivity.localMap M μ = cellularAutomaton γ φ := rfl
  have hinj' : Function.Injective (Surjunctivity.localMap M μ) := by
    rw [hloc]
    exact hinj
  have hsurj := h.surjective_localMap M μ hinj'
  rw [hloc] at hsurj
  exact hsurj

/-- A finitely generated group has a finite generating set. -/
theorem closure_eq_top_of_fg {G : Type} [Group G] (h : Group.FG G) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ :=
  h.out

/-- `not_all_surjunctive_groups_sofic`, from the development endpoint's
statement. -/
theorem not_all_surjunctive_groups_sofic_of
    (h : ∃ (E : Type) (_ : Group E), Group.FG E ∧ Surjunctivity.IsSurjunctive E ∧
      ¬ IsSofic E) :
    ¬ ∀ (G : Type) [Group G], IsSurjunctive G → IsSoficGroup G := by
  intro hall
  obtain ⟨E, _, _, hsurj, hns⟩ := h
  exact hns (isSofic_of_isSoficGroup (hall E (isSurjunctive_of_surjunctive hsurj)))

/-- `exists_finitelyGenerated_surjunctive_not_sofic`, from the development
endpoint's statement. -/
theorem exists_finitelyGenerated_surjunctive_not_sofic_of
    (h : ∃ (E : Type) (_ : Group E), Group.FG E ∧ Surjunctivity.IsSurjunctive E ∧
      ¬ IsSofic E) :
    ∃ (G : Type) (_ : Group G), (∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤) ∧
      IsSurjunctive G ∧ ¬ IsSoficGroup G := by
  obtain ⟨E, _, hfg, hsurj, hns⟩ := h
  exact ⟨E, inferInstance, closure_eq_top_of_fg hfg, isSurjunctive_of_surjunctive hsurj,
    fun hs => hns (isSofic_of_isSoficGroup hs)⟩

end

end BowenChapman
