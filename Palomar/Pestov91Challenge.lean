/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Ozawa's question, Pestov's Open Question 9.1: an infinite simple hyperlinear Kazhdan group

N. Ozawa, *About the QWEP conjecture*, Internat. J. Math. 15 (2004) 501–530
(arXiv:math/0306067, 2003), Section 7, page 26 of the arXiv PDF, verbatim:

> It is unknown whether there exists a simple property (T) group Γ which is
> hyperlinear.

This is the first printed form of the question.  V. G. Pestov, *Hyperlinear
and sofic groups: a brief guide*, Bull. Symbolic Logic 14 (2008) 449–480
(arXiv:0804.3968), Section 9, page 21 of the arXiv PDF, prints it with the
sofic form added, verbatim:

> **Open question 9.1** (Cf. Ozawa [64]). Let G be an infinite simple group
> with Kazhdan's property (T). Can it be hyperlinear (sofic)?

The two theorems below answer **yes**, in both of the question's forms:

* `exists_infinite_simple_propertyT_hyperlinear` is the hyperlinear form,
  Ozawa's question;
* `exists_infinite_simple_propertyT_sofic` is the parenthetical sofic form,
  which is the stronger of the two because sofic groups are hyperlinear.

## Vocabulary

Everything except the definitions in the shared block is Mathlib's: `Infinite`
is Mathlib's infinitude and `IsSimpleGroup` is Mathlib's simplicity, namely
that the group is nontrivial and every normal subgroup is `⊥` or `⊤`.

* `IsKazhdanPair G Q ε` is the textbook Kazhdan pair for a discrete group
  (Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Definition 1.1.3):
  every unitary representation on a complex Hilbert space that carries a unit
  vector moved less than `ε` by every element of the finite set `Q` has a
  nonzero invariant vector.  `HasPropertyT G` asks for some such pair, which is
  Kazhdan's property `(T)`.  For a discrete group the compact Kazhdan sets are
  the finite ones.  The Hilbert spaces range over `Type` with no separability
  assumption, and nothing is lost by the universe: restricted to the closed
  span of one orbit, a representation of a group in `Type` lives on a Hilbert
  space in `Type`.
* `IsSoficGroup G` is soficity in the finite-set normalized-Hamming form: for
  every finite `F ⊆ G` and `ε > 0` there is a map from `G` to the permutations
  of a nonempty finite set that is `ε`-multiplicative on `F` and separates
  distinct elements of `F` by normalized Hamming distance at least `1 - ε`.
  The block is the one already used by `Palomar/BowenChapmanChallenge.lean`.
* `IsHyperlinearGroup G` is the same local formulation with **unitary
  matrices** in place of permutations and the normalized Hilbert–Schmidt
  metric in place of the Hamming metric: `hsDistSq` is the squared normalized
  Hilbert–Schmidt distance, and the separation threshold is `2 - ε` because two
  permutation matrices at Hamming distance `1` sit at squared Hilbert–Schmidt
  distance `2`.

Pestov's Definitions 3.1 and 3.2 (page 6) make a group sofic, respectively
hyperlinear, when it embeds in a metric ultraproduct of symmetric groups,
respectively of unitary groups.  His Theorems 3.5 (page 8) and 3.6 (page 9)
characterize these by local conditions that the block's forms imply, so a group
satisfying the block's definitions answers Question 9.1.

All groups are quantified over `Type`, where the witness lives.  The solution's
witness is `EL₃(LC(X, 𝔽₂) ⋊ ℤ)` for the binary Toeplitz subshift `X`; the two
theorems are existence statements and register nothing about other fields or
other subshifts.

The prose of this module was written by Claude (Anthropic).
-/

namespace Pestov91

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/Pestov91Challenge.lean` and `Palomar/Pestov91Solution.lean`)

/-- A Kazhdan pair for a discrete group (Bekka–de la Harpe–Valette,
*Kazhdan's Property (T)*, Definitions 1.1.1 and 1.1.3): every unitary
representation on a complex Hilbert space with a `(Q,ε)`-almost invariant unit
vector has a nonzero invariant vector.  Since `Q` is finite, the supremum in
Definition 1.1.1 is a maximum, so the strict bound is asked element by
element. -/
def IsKazhdanPair (G : Type) [Group G] (Q : Finset G) (ε : ℝ) : Prop :=
  0 < ε ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
      ∀ ρ : G →* (E ≃ₗᵢ[ℂ] E), ∀ x : E, ‖x‖ = 1 →
        (∀ q ∈ Q, ‖ρ q x - x‖ < ε) →
          ∃ y : E, y ≠ 0 ∧ ∀ g : G, ρ g y = y

/-- Kazhdan's property `(T)`: some finite set and some positive tolerance form
a Kazhdan pair.  Definition 1.1.3 of Bekka–de la Harpe–Valette asks for a
compact Kazhdan set, and the compact subsets of a discrete group are the finite
ones. -/
def HasPropertyT (G : Type) [Group G] : Prop :=
  ∃ (Q : Finset G) (ε : ℝ), IsKazhdanPair G Q ε

/-- A finite index type for permutation and matrix models. -/
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

/-- The proportion of points where two finite permutations differ: the
normalized Hamming distance of Pestov, arXiv:0804.3968, Example 2.3 (page 5). -/
def hammingDist (Y : FiniteCarrier) (p q : Equiv.Perm Y) : ℝ :=
  ((Finset.univ.filter fun y : Y ↦ p y ≠ q y).card : ℝ) / Fintype.card Y

/-- Soficity in the finite-set normalized-Hamming formulation.  It is equivalent
to the local criterion of Pestov, Theorem 3.5 (page 8), which asks
multiplicativity only when `gh ∈ F`, closeness of `θ(e)` to the identity, and
separation `1/4` in place of `1 - ε` (`isSoficGroup_iff_isPestovSofic` in
`Palomar/Pestov91ModelTests.lean`). -/
def IsSoficGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (σ : G → Equiv.Perm Y),
      0 < Fintype.card Y ∧
      (∀ g ∈ F, ∀ h ∈ F, hammingDist Y (σ (g * h)) (σ g * σ h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 1 - ε ≤ hammingDist Y (σ g) (σ h))

/-- The squared normalized Hilbert–Schmidt distance between two matrices
indexed by a finite carrier: the square of the distance of Pestov, Example 2.7
(page 6), normalized so that the identity has norm one. -/
def hsDistSq (Y : FiniteCarrier) (A B : Matrix Y Y ℂ) : ℝ :=
  (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)) / Fintype.card Y

/-- Hyperlinearity in the finite-set normalized-Hilbert–Schmidt formulation.
Pestov's Theorem 3.6 (page 9) is the same local criterion with separation `1/4`;
by Remark 3.7 (page 9) the separation can be taken as close to `√2` as desired,
which is `2 - ε` for the squared distance. -/
def IsHyperlinearGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (σ : G → Matrix Y Y ℂ),
      0 < Fintype.card Y ∧
      (∀ g : G, σ g ∈ Matrix.unitaryGroup Y ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, hsDistSq Y (σ (g * h)) (σ g * σ h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 2 - ε ≤ hsDistSq Y (σ g) (σ h))

-- END SHARED BLOCK

/-- **Ozawa's question, the hyperlinear form of Open question 9.1, has a
positive answer**: some infinite simple group with Kazhdan's property `(T)`
is hyperlinear. -/
theorem exists_infinite_simple_propertyT_hyperlinear :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup G ∧ HasPropertyT G ∧
      IsHyperlinearGroup G := by
  sorry

/-- **The sofic form of Open question 9.1, Pestov's addition to Ozawa's
question, has a positive answer**: some infinite simple group with Kazhdan's
property `(T)` is sofic. -/
theorem exists_infinite_simple_propertyT_sofic :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup G ∧ HasPropertyT G ∧
      IsSoficGroup G := by
  sorry

end

end Pestov91
