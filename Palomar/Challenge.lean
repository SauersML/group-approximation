/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.Order.Field

/-!
# An explicit finitely presented sofic group that is not MF

A countable discrete group is **MF** (matricial field, in the sense of
Carrión–Dadarlat–Eckhardt) if it embeds in the unitary group of a matrix
quotient `∏ₙ M_{dₙ}(ℂ) / ⊕ₙ M_{dₙ}(ℂ)`; equivalently, if it admits
finite-dimensional approximate unitary representations whose multiplicative
errors tend to zero **in operator norm** and which separate distinct group
elements.  The *MF conjecture* asked whether every countable group is MF.

This file states, and the accompanying `Solution` module proves, that the
conjecture is false, with an explicit finitely presented counterexample.

## What is claimed

Let `E` be the group on the eight generators `v₁,v₂,v₃,x,y,z,t,c` with the
forty-one relators written out below (twenty presenting the affine base
`ℤ³ ⋊ SL₃(ℤ)`, six making `t` conjugate the base into its doubling image,
seven making `c` an involution centralising the base, and eight making the
distinguished word central), and let

  `w = [tct⁻¹, v₁(tct⁻¹)v₁⁻¹]`.

Then `E` is finitely presented, `w` is a nontrivial central involution, and
the same group carries finite-dimensional models in two of the three standard
metrics but not in the third:

* **permutations, normalized Hamming distance** — `E` is sofic;
* **unitaries, normalized Hilbert–Schmidt distance** — `E` is hyperlinear;
* **unitaries, operator norm** — `E` is *not* MF.

The obstruction is exhibited, not merely asserted: every operator-norm
asymptotic unitary representation of `E` sends `w` to the identity, while
`w ≠ 1` in `E`.  For the same reason every finite-dimensional linear
representation of `E` over every field, and every homomorphism from `E` to a
finite group, kills `w`; so `E` is not residually finite-dimensional, not
LEF, and not residually finite.

Consequently soficity and hyperlinearity do not imply the MF property, and
the operator-norm approximation problem is genuinely stronger than the
Hamming and Hilbert–Schmidt ones.

## How the MF property is formalized here

The definition of MF used above quantifies over homomorphisms into the
unitary group of the matrix quotient `𝒬`.  That unitary group is canonically
isomorphic to `∏ₙ 𝒰(dₙ)` modulo the sequences converging to `1` in operator
norm, so a homomorphism into it is the same datum as a sequence of maps into
unitary groups whose multiplicative defects vanish in operator norm; and the
resulting property is in turn equivalent to the local form used in
`IsMFGroup` below, with separation constant `1`.  Both equivalences are
proved in the accompanying development (`isCDEOperatorMF_iff_isOperatorMF`
and `isOperatorMF_iff_isNormApproximable_one`, packaged as
`manuscriptMFDefinitionEquivalences`), and the corresponding statement about
the matrix quotient itself is proved there as well.  The local form is used
here because it is elementary: it mentions only complex matrices and the
operator norm, so the statement below can be read against Mathlib alone.

The two obstruction clauses are stated in both available strengths: the
asymptotic-representation clause says every operator-norm asymptotic unitary
representation kills `w`, which is exactly "every homomorphism `E → 𝒰(𝒬)`
kills `w`" after the identification above; and the `¬ IsMFGroup E` clause is
the resulting failure of the MF property itself.

## Provenance

The mechanism combines a property-(T) base with one-sided conjugation and a
Clifford sign, and is the subject of the accompanying paper.  Neighbouring
work on the nonsofic problem uses a related group-theoretic configuration;
this development claims neither that configuration nor the compression
architecture around it.  Full attribution is recorded in the repository's
credit and priority audit.
-/

namespace ExplicitNonMF

open scoped Matrix.Norms.L2Operator

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical with `Palomar/Solution.lean`)

/-! ## Finite models

Every model below lives on a finite set.  Bundling the finiteness and
decidable-equality data keeps the statements free of instance binders; the
bundle carries no information beyond "a finite set". -/

/-- A finite type together with the two instances a finite permutation or
matrix model needs. -/
structure FiniteCarrier where
  /-- The underlying set of the model. -/
  carrier : Type
  /-- Finiteness of that set. -/
  fintype : Fintype carrier
  /-- Decidable equality on it, used to index matrices and to count the
  points at which two permutations disagree. -/
  decidableEq : DecidableEq carrier

instance finiteCarrierCoeSort : CoeSort FiniteCarrier Type :=
  ⟨FiniteCarrier.carrier⟩

@[reducible, instance] def finiteCarrierFintype (Y : FiniteCarrier) :
    Fintype Y :=
  Y.fintype

@[reducible, instance] def finiteCarrierDecidableEq (Y : FiniteCarrier) :
    DecidableEq Y :=
  Y.decidableEq

/-! ## The three approximation properties -/

/-- The **normalized Hamming distance** between two permutations of a finite
set: the proportion of points at which they disagree. -/
def hammingDist (Y : FiniteCarrier) (p q : Equiv.Perm Y) : ℝ :=
  ((Finset.univ.filter fun y : Y ↦ p y ≠ q y).card : ℝ) / Fintype.card Y

/-- The square of the **normalized Hilbert–Schmidt distance** between two
matrices: the sum of the squared moduli of the entries of the difference,
divided by the size of the index set. -/
def hsDistSq (Y : FiniteCarrier) (A B : Matrix Y Y ℂ) : ℝ :=
  (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)) / Fintype.card Y

/-- **Soficity**, in the standard local form: for every finite test set `F`
and every tolerance `ε > 0` there is a nonempty finite set with a map from
the group to its permutations which is multiplicative within `ε` on `F` and
separates distinct elements of `F` by at least `1 - ε`, both measured in
normalized Hamming distance. -/
def IsSoficGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (σ : G → Equiv.Perm Y),
      0 < Fintype.card Y ∧
      (∀ g ∈ F, ∀ h ∈ F, hammingDist Y (σ (g * h)) (σ g * σ h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 1 - ε ≤ hammingDist Y (σ g) (σ h))

/-- **Hyperlinearity**: the same local scheme with unitary matrices in place
of permutations and the normalized Hilbert–Schmidt metric in place of the
Hamming metric.  The separation constant is `2 - ε` because the translation
from Hamming doubles distances: two perfectly separated permutation unitaries
sit at squared normalized Hilbert–Schmidt distance `2`. -/
def IsHyperlinearGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (U : G → Matrix Y Y ℂ),
      0 < Fintype.card Y ∧
      (∀ g, U g ∈ Matrix.unitaryGroup Y ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, hsDistSq Y (U (g * h)) (U g * U h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 2 - ε ≤ hsDistSq Y (U g) (U h))

/-- **The MF property**, in the local operator-norm form: the same scheme
again, with the multiplicative defect and the separation both measured in the
operator norm, and with separation constant `1`.  For a countable group this
is equivalent to admitting an injective homomorphism into the unitary group
of a matrix quotient `∏ₙ M_{dₙ}(ℂ)/⊕ₙ M_{dₙ}(ℂ)`, which is the definition of
Carrión–Dadarlat–Eckhardt; see the module documentation. -/
def IsMFGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (U : G → Matrix Y Y ℂ),
      0 < Fintype.card Y ∧
      (∀ g, U g ∈ Matrix.unitaryGroup Y ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, ‖U (g * h) - U g * U h‖ ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 1 ≤ ‖U g - U h‖)

/-! ## The group `E`

The alphabet is the six base letters `v₁,v₂,v₃,x,y,z` followed by the two
adjoined letters `t` and `c`, so `E` has eight generators. -/

/-- Catch-all decidable equality for the alphabets and free groups below.  It
sits in the discrimination tree's catch-all bucket, so any specific instance
takes precedence over it. -/
local instance literalDecidableEq {α : Type*} : DecidableEq α :=
  Classical.decEq α

/-- The six base letters, ordered as `v₁,v₂,v₃,x,y,z`. -/
abbrev BaseGenerator := Fin 6

/-- The full alphabet: the six base letters followed by `t` and `c`.  It has
eight elements. -/
abbrev Generator := BaseGenerator ⊕ Fin 2

/-- The index of the base letter `v₁`. -/
abbrev v1Index : BaseGenerator := 0
/-- The index of the base letter `v₂`. -/
abbrev v2Index : BaseGenerator := 1
/-- The index of the base letter `v₃`. -/
abbrev v3Index : BaseGenerator := 2
/-- The index of the base letter `x`. -/
abbrev xIndex : BaseGenerator := 3
/-- The index of the base letter `y`. -/
abbrev yIndex : BaseGenerator := 4
/-- The index of the base letter `z`. -/
abbrev zIndex : BaseGenerator := 5

/-- A base letter, as a letter of the full alphabet. -/
abbrev Generator.base (i : BaseGenerator) : Generator := Sum.inl i
/-- The stable letter `t`. -/
abbrev Generator.stable : Generator := Sum.inr 0
/-- The lamp letter `c`. -/
abbrev Generator.lamp : Generator := Sum.inr 1

/-- The free-group letter `v₁` over the base alphabet. -/
abbrev bv1 : FreeGroup BaseGenerator := FreeGroup.of v1Index
/-- The free-group letter `v₂` over the base alphabet. -/
abbrev bv2 : FreeGroup BaseGenerator := FreeGroup.of v2Index
/-- The free-group letter `v₃` over the base alphabet. -/
abbrev bv3 : FreeGroup BaseGenerator := FreeGroup.of v3Index
/-- The free-group letter `x` over the base alphabet. -/
abbrev bx : FreeGroup BaseGenerator := FreeGroup.of xIndex
/-- The free-group letter `y` over the base alphabet. -/
abbrev bY : FreeGroup BaseGenerator := FreeGroup.of yIndex
/-- The free-group letter `z` over the base alphabet. -/
abbrev bz : FreeGroup BaseGenerator := FreeGroup.of zIndex

/-- A base letter as a word in the full alphabet. -/
abbrev vertexLetter (i : BaseGenerator) : FreeGroup Generator :=
  FreeGroup.of (Generator.base i)

/-- The letter `v₁` as a word in the full alphabet. -/
abbrev v1Word : FreeGroup Generator := vertexLetter v1Index
/-- The letter `v₂` as a word in the full alphabet. -/
abbrev v2Word : FreeGroup Generator := vertexLetter v2Index
/-- The letter `v₃` as a word in the full alphabet. -/
abbrev v3Word : FreeGroup Generator := vertexLetter v3Index
/-- The letter `x` as a word in the full alphabet. -/
abbrev xWord : FreeGroup Generator := vertexLetter xIndex
/-- The letter `y` as a word in the full alphabet. -/
abbrev yWord : FreeGroup Generator := vertexLetter yIndex
/-- The letter `z` as a word in the full alphabet. -/
abbrev zWord : FreeGroup Generator := vertexLetter zIndex
/-- The stable letter `t` as a word. -/
abbrev stableWord : FreeGroup Generator := FreeGroup.of Generator.stable
/-- The lamp letter `c` as a word. -/
abbrev lampWord : FreeGroup Generator := FreeGroup.of Generator.lamp

/-- The commutator word, with the convention `[g,h] = g h g⁻¹ h⁻¹`. -/
def commutatorWord {G : Type*} [Group G] (g h : G) : G :=
  g * h * g⁻¹ * h⁻¹

/-- Embed words in the six base letters into the full alphabet. -/
def embedBaseWord : FreeGroup BaseGenerator →* FreeGroup Generator :=
  FreeGroup.lift fun i ↦ vertexLetter i

/-! ### The twenty base relators

These present the affine group `ℤ³ ⋊ SL₃(ℤ)`: the first eight are the
Conder–Robertson–Williams presentation of `SL₃(ℤ)` in the generators
`x, y, z`, the next three make the translations commute, and the last nine
give the action of the linear generators on them. -/

/-- `x³ = 1`. -/
abbrev baseRelXCube : FreeGroup BaseGenerator := bx ^ 3
/-- `y³ = 1`. -/
abbrev baseRelYCube : FreeGroup BaseGenerator := bY ^ 3
/-- `z² = 1`. -/
abbrev baseRelZSq : FreeGroup BaseGenerator := bz ^ 2
/-- `(xz)³ = 1`. -/
abbrev baseRelXZCube : FreeGroup BaseGenerator := (bx * bz) ^ 3
/-- `(yz)³ = 1`. -/
abbrev baseRelYZCube : FreeGroup BaseGenerator := (bY * bz) ^ 3
/-- `(x⁻¹zxy)² = 1`. -/
abbrev baseRelXInvZXY : FreeGroup BaseGenerator := (bx⁻¹ * bz * bx * bY) ^ 2
/-- `(y⁻¹zyx)² = 1`. -/
abbrev baseRelYInvZYX : FreeGroup BaseGenerator := (bY⁻¹ * bz * bY * bx) ^ 2
/-- `(xy)⁶ = 1`. -/
abbrev baseRelXYSix : FreeGroup BaseGenerator := (bx * bY) ^ 6

/-- `[v₁,v₂] = 1`. -/
abbrev baseRelV12 : FreeGroup BaseGenerator := commutatorWord bv1 bv2
/-- `[v₁,v₃] = 1`. -/
abbrev baseRelV13 : FreeGroup BaseGenerator := commutatorWord bv1 bv3
/-- `[v₂,v₃] = 1`. -/
abbrev baseRelV23 : FreeGroup BaseGenerator := commutatorWord bv2 bv3

/-- `x v₁ x⁻¹ = v₃`. -/
abbrev baseRelXV1 : FreeGroup BaseGenerator := bx * bv1 * bx⁻¹ * bv3⁻¹
/-- `x v₂ x⁻¹ = v₁`. -/
abbrev baseRelXV2 : FreeGroup BaseGenerator := bx * bv2 * bx⁻¹ * bv1⁻¹
/-- `x v₃ x⁻¹ = v₂`. -/
abbrev baseRelXV3 : FreeGroup BaseGenerator := bx * bv3 * bx⁻¹ * bv2⁻¹
/-- `y v₁ y⁻¹ = v₁`. -/
abbrev baseRelYV1 : FreeGroup BaseGenerator := bY * bv1 * bY⁻¹ * bv1⁻¹
/-- `y v₂ y⁻¹ = v₂⁻¹v₃`. -/
abbrev baseRelYV2 : FreeGroup BaseGenerator :=
  bY * bv2 * bY⁻¹ * (bv2⁻¹ * bv3)⁻¹
/-- `y v₃ y⁻¹ = v₁v₂⁻¹`. -/
abbrev baseRelYV3 : FreeGroup BaseGenerator :=
  bY * bv3 * bY⁻¹ * (bv1 * bv2⁻¹)⁻¹
/-- `z v₁ z⁻¹ = v₂v₃⁻¹`. -/
abbrev baseRelZV1 : FreeGroup BaseGenerator :=
  bz * bv1 * bz⁻¹ * (bv2 * bv3⁻¹)⁻¹
/-- `z v₂ z⁻¹ = v₁v₃⁻¹`. -/
abbrev baseRelZV2 : FreeGroup BaseGenerator :=
  bz * bv2 * bz⁻¹ * (bv1 * bv3⁻¹)⁻¹
/-- `z v₃ z⁻¹ = v₃⁻¹`. -/
abbrev baseRelZV3 : FreeGroup BaseGenerator :=
  bz * bv3 * bz⁻¹ * (bv3⁻¹)⁻¹

/-- Exactly the twenty base relators. -/
def baseRelators : Finset (FreeGroup BaseGenerator) :=
  [baseRelXCube, baseRelYCube, baseRelZSq, baseRelXZCube,
   baseRelYZCube, baseRelXInvZXY, baseRelYInvZYX, baseRelXYSix,
   baseRelV12, baseRelV13, baseRelV23,
   baseRelXV1, baseRelXV2, baseRelXV3,
   baseRelYV1, baseRelYV2, baseRelYV3,
   baseRelZV1, baseRelZV2, baseRelZV3].toFinset

/-! ### The remaining twenty-one relators -/

/-- The right-hand side of the stable-letter relation, as a base word: the
three translations are squared and the three linear generators are fixed. -/
def compressedBaseWord (i : BaseGenerator) : FreeGroup BaseGenerator :=
  if i = v1Index then bv1 ^ 2
  else if i = v2Index then bv2 ^ 2
  else if i = v3Index then bv3 ^ 2
  else if i = xIndex then bx
  else if i = yIndex then bY
  else bz

/-- The right-hand side of the stable-letter relation, in the full
alphabet. -/
def compressedGeneratorWord (i : BaseGenerator) : FreeGroup Generator :=
  embedBaseWord (compressedBaseWord i)

/-- The stable-letter relator `t s t⁻¹ = α(s)` for a base letter `s`. -/
def stableRelator (i : BaseGenerator) : FreeGroup Generator :=
  stableWord * vertexLetter i * stableWord⁻¹ * (compressedGeneratorWord i)⁻¹

/-- The conjugated lamp `d = t c t⁻¹`. -/
abbrev displacedLampWord : FreeGroup Generator :=
  stableWord * lampWord * stableWord⁻¹

/-- The distinguished word `w = [d, v₁ d v₁⁻¹]` with `d = t c t⁻¹`. -/
abbrev markedWord : FreeGroup Generator :=
  commutatorWord displacedLampWord
    (v1Word * displacedLampWord * v1Word⁻¹)

/-- The twenty base relators, transported into the full alphabet. -/
def transportedBaseRelators : Finset (FreeGroup Generator) :=
  baseRelators.image embedBaseWord

/-- The six stable-letter relators. -/
def stableRelators : Finset (FreeGroup Generator) :=
  Finset.univ.image stableRelator

/-- The seven lamp relators: `c² = 1` and `[c, s] = 1` for each of the six
base letters `s`. -/
def lampRelators : Finset (FreeGroup Generator) :=
  {lampWord ^ 2} ∪
    Finset.univ.image (fun i : BaseGenerator ↦
      commutatorWord lampWord (vertexLetter i))

/-- The eight centrality relators `[w, g] = 1`, one for each generator. -/
def markedRelators : Finset (FreeGroup Generator) :=
  Finset.univ.image (fun i : Generator ↦
    commutatorWord markedWord (FreeGroup.of i))

/-- All forty-one relators of `E`: twenty base, six stable-letter, seven
lamp, and eight centrality relators. -/
def relators : Finset (FreeGroup Generator) :=
  transportedBaseRelators ∪ stableRelators ∪ lampRelators ∪ markedRelators

/-- **The group `E`**: eight generators, forty-one relators. -/
abbrev E : Type :=
  PresentedGroup ((relators : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

/-- The canonical map from words in the eight letters to `E`. -/
abbrev wordInE : FreeGroup Generator →* E :=
  PresentedGroup.mk ((relators : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

/-- **The distinguished element** `w = [tct⁻¹, v₁(tct⁻¹)v₁⁻¹]` of `E`. -/
abbrev w : E := wordInE markedWord

-- END SHARED BLOCK

/-! ## The statement -/

/-- **An explicit finitely presented sofic group that is not MF.**

For the group `E` displayed above and its distinguished word `w`:

1. `E` is finitely presented;
2. `w` is a nontrivial central involution of `E`;
3. `E` is sofic — it has permutation models in normalized Hamming distance;
4. `E` is hyperlinear — it has unitary models in normalized
   Hilbert–Schmidt distance;
5. every operator-norm asymptotic unitary representation of `E` sends `w` to
   the identity, which is exactly the statement that every homomorphism from
   `E` into the unitary group of a matrix quotient kills `w`;
6. consequently `E` is **not** MF: no operator-norm models separate its
   elements;
7. and every finite-dimensional linear representation of `E`, over every
   field, also kills `w`; so no such representation is injective.

Clauses 3, 4 and 6 together say that soficity and hyperlinearity do not imply
the MF property.  Clause 2 is what makes 5 and 7 non-vacuous. -/
theorem explicit_fp_sofic_hyperlinear_not_MF :
    Group.IsFinitelyPresented E ∧
    (w ≠ 1 ∧ w ^ 2 = 1 ∧ ∀ g : E, Commute w g) ∧
    IsSoficGroup E ∧
    IsHyperlinearGroup E ∧
    (∀ (Y : ℕ → FiniteCarrier) (U : ∀ n, E → Matrix (Y n) (Y n) ℂ),
        (∀ n g, U n g ∈ Matrix.unitaryGroup (Y n) ℂ) →
        (∀ g h : E, Filter.Tendsto
            (fun n ↦ ‖U n (g * h) - U n g * U n h‖) Filter.atTop (nhds 0)) →
        Filter.Tendsto (fun n ↦ ‖U n w - 1‖) Filter.atTop (nhds 0)) ∧
    ¬ IsMFGroup E ∧
    (∀ (K : Type) (W : Type) [Field K] [AddCommGroup W] [Module K W]
        [FiniteDimensional K W] (π : E →* (Module.End K W)ˣ), π w = 1) := by
  sorry

end

end ExplicitNonMF
