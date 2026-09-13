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
import GroupApproximation.Kazhdan.KazhdanComplex
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Pestov91.WitnessAssembly

/-!
# Proof of the Pestov Open Question 9.1 theorems

This file repeats the challenge's shared block byte for byte, translates the
development's vocabulary into it, and derives the statements
`Palomar/comparator-pestov91.json` selects from the development's infinite
simple LEF group with property `(T)`.

* `hasPropertyT_of_hasKazhdanPropertyTComplex` and
  `hasKazhdanPropertyTComplex_of_hasPropertyT`: the challenge's `HasPropertyT`
  is the development's complex-unitary
  `GroupApproximation.HasKazhdanPropertyTComplex` at universes `{0, 0}`, whose
  Kazhdan pair has the challenge's body word for word.
  `hasPropertyT_iff_hasKazhdanPropertyT` passes to the development's real form
  `GroupApproximation.HasKazhdanPropertyT` through
  `GroupApproximation.hasKazhdanPropertyT_iff_complex`.
* `isSoficGroup_of_isSofic` and `isSofic_of_isSoficGroup`: the challenge's
  `IsSoficGroup` is the development's `GroupApproximation.IsSofic`, with the
  model carrier repackaged.
* `isHyperlinearGroup_of_isHyperlinear` and
  `isHyperlinear_of_isHyperlinearGroup`: the challenge's `IsHyperlinearGroup`
  is the development's `GroupApproximation.IsHyperlinear`, again with the
  carrier repackaged; the two squared Hilbert–Schmidt distances have the same
  body.
* `isSoficGroup_of_isLEF` and `isHyperlinearGroup_of_isSoficGroup`: LEF groups
  are sofic (`GroupApproximation.isSofic_of_isLEF`), and sofic groups are
  hyperlinear (`GroupApproximation.isHyperlinear_of_isSofic`).
* `exists_infinite_simple_propertyT_hyperlinear_of` and
  `exists_infinite_simple_propertyT_sofic_of` carry any infinite simple LEF
  group of the development with property `(T)` into the challenge's two
  statements.
* `exists_infinite_simple_propertyT_hyperlinear` and
  `exists_infinite_simple_propertyT_sofic`: the challenge's two statements.

The development endpoint is
`GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef` in
`GroupApproximation/Pestov91/WitnessAssembly.lean`.  Its group is `EL₃(A)` for
the finitely generated ring `A = LC(X, 𝔽₂) ⋊ ℤ` over the Toeplitz subshift `X`,
through `GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef_of_elementary`
in `GroupApproximation/Pestov91/Assembly.lean`.

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
`wip/pestov91/fidelity/Pestov91ModelTests.lean`). -/
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

open GroupApproximation

/-- The development's complex-unitary property `(T)` gives the challenge's:
`IsKazhdanPairComplex.{0, 0}` has the challenge's `IsKazhdanPair` body. -/
theorem hasPropertyT_of_hasKazhdanPropertyTComplex {G : Type} [Group G]
    (h : HasKazhdanPropertyTComplex.{0, 0} G) : HasPropertyT G :=
  h

/-- The challenge's property `(T)` gives the development's complex-unitary
form. -/
theorem hasKazhdanPropertyTComplex_of_hasPropertyT {G : Type} [Group G]
    (h : HasPropertyT G) : HasKazhdanPropertyTComplex.{0, 0} G :=
  h

/-- The challenge's property `(T)` is the development's, which is stated over
real Hilbert spaces. -/
theorem hasPropertyT_iff_hasKazhdanPropertyT {G : Type} [Group G] :
    HasPropertyT G ↔ HasKazhdanPropertyT.{0, 0} G :=
  ⟨fun h ↦ hasKazhdanPropertyT_iff_complex.mpr (hasKazhdanPropertyTComplex_of_hasPropertyT h),
    fun h ↦ hasPropertyT_of_hasKazhdanPropertyTComplex (hasKazhdanPropertyT_iff_complex.mp h)⟩

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

/-- The development's hyperlinearity gives the challenge's. -/
theorem isHyperlinearGroup_of_isHyperlinear {G : Type} [Group G] (h : IsHyperlinear G) :
    IsHyperlinearGroup G := by
  intro F ε hε
  obtain ⟨m⟩ := h F ε hε
  exact ⟨⟨m.carrier.carrier, m.carrier.fintype, m.carrier.decidableEq⟩,
    m.map, m.nonempty, m.isUnitary, m.multiplicative, m.separated⟩

/-- The challenge's hyperlinearity gives the development's. -/
theorem isHyperlinear_of_isHyperlinearGroup {G : Type} [Group G]
    (h : IsHyperlinearGroup G) : IsHyperlinear G := by
  intro F ε hε
  obtain ⟨Y, σ, hY, hU, hmul, hsep⟩ := h F ε hε
  exact ⟨{ carrier := ⟨Y.carrier, Y.fintype, Y.decidableEq⟩
           nonempty := hY
           map := σ
           isUnitary := hU
           multiplicative := hmul
           separated := hsep }⟩

/-- LEF groups are sofic, in the challenge's vocabulary. -/
theorem isSoficGroup_of_isLEF {G : Type} [Group G] (h : IsLEF G) : IsSoficGroup G :=
  isSoficGroup_of_isSofic (isSofic_of_isLEF h)

/-- Sofic groups are hyperlinear, in the challenge's vocabulary. -/
theorem isHyperlinearGroup_of_isSoficGroup {G : Type} [Group G] (h : IsSoficGroup G) :
    IsHyperlinearGroup G :=
  isHyperlinearGroup_of_isHyperlinear (isHyperlinear_of_isSofic (isSofic_of_isSoficGroup h))

/-- `exists_infinite_simple_propertyT_hyperlinear`, from any infinite simple LEF
group of the development with property `(T)`. -/
theorem exists_infinite_simple_propertyT_hyperlinear_of
    (h : ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E) :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup G ∧ HasPropertyT G ∧
      IsHyperlinearGroup G := by
  obtain ⟨E, _, hinf, hsimple, hT, hlef⟩ := h
  exact ⟨E, inferInstance, hinf, hsimple, hasPropertyT_iff_hasKazhdanPropertyT.mpr hT,
    isHyperlinearGroup_of_isSoficGroup (isSoficGroup_of_isLEF hlef)⟩

/-- `exists_infinite_simple_propertyT_sofic`, from any infinite simple LEF group
of the development with property `(T)`. -/
theorem exists_infinite_simple_propertyT_sofic_of
    (h : ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E) :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup G ∧ HasPropertyT G ∧
      IsSoficGroup G := by
  obtain ⟨E, _, hinf, hsimple, hT, hlef⟩ := h
  exact ⟨E, inferInstance, hinf, hsimple, hasPropertyT_iff_hasKazhdanPropertyT.mpr hT,
    isSoficGroup_of_isLEF hlef⟩

/-- **Open question 9.1 has a positive answer**: some infinite simple group
with Kazhdan's property `(T)` is hyperlinear. -/
theorem exists_infinite_simple_propertyT_hyperlinear :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup G ∧ HasPropertyT G ∧
      IsHyperlinearGroup G :=
  exists_infinite_simple_propertyT_hyperlinear_of
    GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef

/-- **The sofic form of question 9.1 has a positive answer**: some infinite
simple group with Kazhdan's property `(T)` is sofic. -/
theorem exists_infinite_simple_propertyT_sofic :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup G ∧ HasPropertyT G ∧
      IsSoficGroup G :=
  exists_infinite_simple_propertyT_sofic_of
    GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef

end

end Pestov91
