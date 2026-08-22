/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.Order.Field
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.LiteralSoficAssembly
import GroupApproximation.Sofic.LiteralFiniteDimensionalObstruction
import GroupApproximation.Sofic.LiteralUniformObstruction
import GroupApproximation.Sofic.LiteralSixGenerator
import GroupApproximation.Sofic.NormMFConsequences
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Meta.AxiomGuard

/-!
# Proof of the advertised statement

The declaration block below is byte-identical with the one in
`Palomar/Challenge.lean`, and so is the statement of the compared theorem.
Everything after it is the proof, which may use the whole development.

The duplication is forced by the protocol rather than chosen.  Comparator
compares the two exported statements structurally and then walks every
constant they mention, requiring each to be identical in both environments;
a constant present in only one file is a mismatch, not a match.  The block
therefore cannot be shared by an import, and
`scripts/check_palomar_submission.py` fails the build when the two copies
drift.  `scripts/check_palomar_statement_match.sh` additionally compares the
statement as elaborated, which text comparison cannot see.

The bridge to the development is definitional, not propositional: the copied
definitions elaborate to the same terms as
`GroupApproximation.LiteralNonMFPresentation.relators`, `…MarkedGroup` and
`…mark`, so the endpoints proved there apply directly.  `E_eq` and `w_eq`
below pin that down and stop compiling the moment it stops being true.

This module introduces no mathematics.  Every clause is discharged by an
endpoint of the development, named at its bullet.
-/

namespace ExplicitNonMF

open scoped Matrix.Norms.L2Operator

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical with `PalomarSolution.lean`)

/-! ## Finite models

Every model below lives on a finite set.  Bundling the finiteness and
decidable-equality data keeps the statements free of instance binders; the
bundle carries no information beyond "a finite set". -/

/-- A finite type together with the two instances a finite permutation or
matrix model needs.  It carries no information beyond the underlying finite
set. -/
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

/-! ## The three approximation properties

Each of the three is the same local scheme -- a finite model of every
accuracy on every finite test set -- differing only in what the models are
and in which metric the two defects are measured. -/

/-- The **normalized Hamming distance** between two permutations of a finite
set: the proportion of points at which they disagree.  It is `0` exactly when
they agree and `1` when they disagree everywhere. -/
def hammingDist (Y : FiniteCarrier) (p q : Equiv.Perm Y) : ℝ :=
  ((Finset.univ.filter fun y : Y ↦ p y ≠ q y).card : ℝ) / Fintype.card Y

/-- The square of the **normalized Hilbert-Schmidt distance** between two
matrices: the sum of the squared moduli of the entries of the difference,
divided by the size of the index set.  For unitaries this is
`2 - 2 Re tr(A* B)` with the normalized trace. -/
def hsDistSq (Y : FiniteCarrier) (A B : Matrix Y Y ℂ) : ℝ :=
  (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)) / Fintype.card Y

/-- **Soficity**, in the standard local form.  For every finite test set `F` and
every tolerance `ε > 0` there is a nonempty finite set and a map from the
group to its permutations which is multiplicative within `ε` on `F` and
separates distinct elements of `F` by at least `1 - ε`, both measured in
normalized Hamming distance.  Equivalently: `G` embeds in a metric
ultraproduct of finite symmetric groups with the Hamming length function. -/
def IsSoficGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (σ : G → Equiv.Perm Y),
      0 < Fintype.card Y ∧
      (∀ g ∈ F, ∀ h ∈ F, hammingDist Y (σ (g * h)) (σ g * σ h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 1 - ε ≤ hammingDist Y (σ g) (σ h))

/-- **Hyperlinearity**: the same local scheme with unitary matrices in place of
permutations and the normalized Hilbert-Schmidt metric in place of the
Hamming metric.  The separation constant is `2 - ε` rather than `1 - ε`
because the translation from Hamming doubles distances: two permutation
unitaries with disjoint supports sit at squared normalized Hilbert-Schmidt
distance `2`.  Every sofic group is hyperlinear. -/
def IsHyperlinearGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (U : G → Matrix Y Y ℂ),
      0 < Fintype.card Y ∧
      (∀ g, U g ∈ Matrix.unitaryGroup Y ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, hsDistSq Y (U (g * h)) (U g * U h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 2 - ε ≤ hsDistSq Y (U g) (U h))

/-- **The MF property** in the sense of Carrión-Dadarlat-Eckhardt, in its local
operator-norm form: the same scheme again, with the multiplicative defect and
the separation both measured in the operator norm and the separation constant
fixed at `1`.  For a countable group this is equivalent to admitting an
injective homomorphism into the unitary group of a matrix quotient
`∏ₙ M_{dₙ}(ℂ) / ⊕ₙ M_{dₙ}(ℂ)`; see the module documentation for where that
equivalence is proved. -/
def IsMFGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (U : G → Matrix Y Y ℂ),
      0 < Fintype.card Y ∧
      (∀ g, U g ∈ Matrix.unitaryGroup Y ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, ‖U (g * h) - U g * U h‖ ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 1 ≤ ‖U g - U h‖)

/-! ## The group `E`

The alphabet is the six base letters `v₁, v₂, v₃, x, y, z` followed by the
two adjoined letters `t` and `c`, so `E` has eight generators. -/

/-- Catch-all decidable equality for the alphabets and free groups below.  It
sits in the discrimination tree's catch-all bucket, so any specific instance
takes precedence over it.  Nothing in the statement depends on which
instance is found: the relator set is a finite set of free-group words either
way. -/
local instance literalDecidableEq {α : Type*} : DecidableEq α :=
  Classical.decEq α

/-- The six base letters, ordered as `v₁, v₂, v₃, x, y, z`. -/
abbrev BaseGenerator := Fin 6

/-- The full alphabet: the six base letters followed by `t` and `c`.  It has
eight elements, which is the generator count of `E`. -/
abbrev Generator := BaseGenerator ⊕ Fin 2

/-- The index of the base letter `v₁`, the first translation. -/
abbrev v1Index : BaseGenerator := 0
/-- The index of the base letter `v₂`, the second translation. -/
abbrev v2Index : BaseGenerator := 1
/-- The index of the base letter `v₃`, the third translation. -/
abbrev v3Index : BaseGenerator := 2
/-- The index of the base letter `x`, the first linear generator. -/
abbrev xIndex : BaseGenerator := 3
/-- The index of the base letter `y`, the second linear generator. -/
abbrev yIndex : BaseGenerator := 4
/-- The index of the base letter `z`, the third linear generator. -/
abbrev zIndex : BaseGenerator := 5

/-- A base letter, viewed as a letter of the full alphabet. -/
abbrev Generator.base (i : BaseGenerator) : Generator := Sum.inl i
/-- The stable letter `t`, which conjugates the base onto its doubling image. -/
abbrev Generator.stable : Generator := Sum.inr 0
/-- The letter `c`, an involution centralising the base. -/
abbrev Generator.lamp : Generator := Sum.inr 1

/-- The letter `v₁` as a word over the base alphabet. -/
abbrev bv1 : FreeGroup BaseGenerator := FreeGroup.of v1Index
/-- The letter `v₂` as a word over the base alphabet. -/
abbrev bv2 : FreeGroup BaseGenerator := FreeGroup.of v2Index
/-- The letter `v₃` as a word over the base alphabet. -/
abbrev bv3 : FreeGroup BaseGenerator := FreeGroup.of v3Index
/-- The letter `x` as a word over the base alphabet. -/
abbrev bx : FreeGroup BaseGenerator := FreeGroup.of xIndex
/-- The letter `y` as a word over the base alphabet. -/
abbrev bY : FreeGroup BaseGenerator := FreeGroup.of yIndex
/-- The letter `z` as a word over the base alphabet. -/
abbrev bz : FreeGroup BaseGenerator := FreeGroup.of zIndex

/-- A base letter as a word over the full alphabet. -/
abbrev vertexLetter (i : BaseGenerator) : FreeGroup Generator :=
  FreeGroup.of (Generator.base i)

/-- The letter `v₁` as a word over the full alphabet. -/
abbrev v1Word : FreeGroup Generator := vertexLetter v1Index
/-- The letter `v₂` as a word over the full alphabet. -/
abbrev v2Word : FreeGroup Generator := vertexLetter v2Index
/-- The letter `v₃` as a word over the full alphabet. -/
abbrev v3Word : FreeGroup Generator := vertexLetter v3Index
/-- The letter `x` as a word over the full alphabet. -/
abbrev xWord : FreeGroup Generator := vertexLetter xIndex
/-- The letter `y` as a word over the full alphabet. -/
abbrev yWord : FreeGroup Generator := vertexLetter yIndex
/-- The letter `z` as a word over the full alphabet. -/
abbrev zWord : FreeGroup Generator := vertexLetter zIndex
/-- The letter `t` as a word over the full alphabet. -/
abbrev stableWord : FreeGroup Generator := FreeGroup.of Generator.stable
/-- The letter `c` as a word over the full alphabet. -/
abbrev lampWord : FreeGroup Generator := FreeGroup.of Generator.lamp

/-- The commutator word, with the convention `[g, h] = g h g⁻¹ h⁻¹`.  Imposing
it as a relator is imposing `g h = h g`. -/
def commutatorWord {G : Type*} [Group G] (g h : G) : G :=
  g * h * g⁻¹ * h⁻¹

/-- Embed a word in the six base letters into the full alphabet. -/
def embedBaseWord : FreeGroup BaseGenerator →* FreeGroup Generator :=
  FreeGroup.lift fun i ↦ vertexLetter i

/-! ### The twenty base relators

These present the affine group `ℤ³ ⋊ SL₃(ℤ)`.  The first eight are the
Conder-Robertson-Williams presentation of `SL₃(ℤ)` on `x, y, z`; the next
three make the three translations commute; the last nine give the action of
each linear generator on each translation. -/

/-- `x³ = 1`. -/
abbrev baseRelXCube : FreeGroup BaseGenerator := bx ^ 3
/-- `y³ = 1`. -/
abbrev baseRelYCube : FreeGroup BaseGenerator := bY ^ 3
/-- `z² = 1`. -/
abbrev baseRelZSq : FreeGroup BaseGenerator := bz ^ 2
/-- `(x z)³ = 1`. -/
abbrev baseRelXZCube : FreeGroup BaseGenerator := (bx * bz) ^ 3
/-- `(y z)³ = 1`. -/
abbrev baseRelYZCube : FreeGroup BaseGenerator := (bY * bz) ^ 3
/-- `(x⁻¹ z x y)² = 1`. -/
abbrev baseRelXInvZXY : FreeGroup BaseGenerator := (bx⁻¹ * bz * bx * bY) ^ 2
/-- `(y⁻¹ z y x)² = 1`. -/
abbrev baseRelYInvZYX : FreeGroup BaseGenerator := (bY⁻¹ * bz * bY * bx) ^ 2
/-- `(x y)⁶ = 1`.  With the seven relations above this presents `SL₃(ℤ)` on
`x, y, z`. -/
abbrev baseRelXYSix : FreeGroup BaseGenerator := (bx * bY) ^ 6

/-- `v₁ v₂ = v₂ v₁`. -/
abbrev baseRelV12 : FreeGroup BaseGenerator := commutatorWord bv1 bv2
/-- `v₁ v₃ = v₃ v₁`. -/
abbrev baseRelV13 : FreeGroup BaseGenerator := commutatorWord bv1 bv3
/-- `v₂ v₃ = v₃ v₂`.  With the two above, the three translations commute, so
they generate a copy of `ℤ³`. -/
abbrev baseRelV23 : FreeGroup BaseGenerator := commutatorWord bv2 bv3

/-- `x v₁ x⁻¹ = v₃`. -/
abbrev baseRelXV1 : FreeGroup BaseGenerator := bx * bv1 * bx⁻¹ * bv3⁻¹
/-- `x v₂ x⁻¹ = v₁`. -/
abbrev baseRelXV2 : FreeGroup BaseGenerator := bx * bv2 * bx⁻¹ * bv1⁻¹
/-- `x v₃ x⁻¹ = v₂`: `x` cycles the three translations. -/
abbrev baseRelXV3 : FreeGroup BaseGenerator := bx * bv3 * bx⁻¹ * bv2⁻¹
/-- `y v₁ y⁻¹ = v₁`. -/
abbrev baseRelYV1 : FreeGroup BaseGenerator := bY * bv1 * bY⁻¹ * bv1⁻¹
/-- `y v₂ y⁻¹ = v₂⁻¹ v₃`. -/
abbrev baseRelYV2 : FreeGroup BaseGenerator :=
  bY * bv2 * bY⁻¹ * (bv2⁻¹ * bv3)⁻¹
/-- `y v₃ y⁻¹ = v₁ v₂⁻¹`. -/
abbrev baseRelYV3 : FreeGroup BaseGenerator :=
  bY * bv3 * bY⁻¹ * (bv1 * bv2⁻¹)⁻¹
/-- `z v₁ z⁻¹ = v₂ v₃⁻¹`. -/
abbrev baseRelZV1 : FreeGroup BaseGenerator :=
  bz * bv1 * bz⁻¹ * (bv2 * bv3⁻¹)⁻¹
/-- `z v₂ z⁻¹ = v₁ v₃⁻¹`. -/
abbrev baseRelZV2 : FreeGroup BaseGenerator :=
  bz * bv2 * bz⁻¹ * (bv1 * bv3⁻¹)⁻¹
/-- `z v₃ z⁻¹ = v₃⁻¹`.  With the eight above, the linear generators act on the
translation lattice by their matrices, so the base is `ℤ³ ⋊ SL₃(ℤ)`. -/
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

/-! ### The remaining twenty-one relators

Six make `t` conjugate the base onto its doubling image, seven make `c` an
involution centralising the base, and eight make the distinguished word
central. -/

/-- The right-hand side of the stable-letter relation, as a base word: each of
the three translations is squared and each of the three linear generators is
fixed.  This is the doubling endomorphism `(v, A) ↦ (2v, A)` of
`ℤ³ ⋊ SL₃(ℤ)`, which is injective and not surjective. -/
def compressedBaseWord (i : BaseGenerator) : FreeGroup BaseGenerator :=
  if i = v1Index then bv1 ^ 2
  else if i = v2Index then bv2 ^ 2
  else if i = v3Index then bv3 ^ 2
  else if i = xIndex then bx
  else if i = yIndex then bY
  else bz

/-- The right-hand side of the stable-letter relation, in the full alphabet. -/
def compressedGeneratorWord (i : BaseGenerator) : FreeGroup Generator :=
  embedBaseWord (compressedBaseWord i)

/-- The stable-letter relator for a base letter `s`: `t s t⁻¹ = α(s)`, where `α`
is the doubling endomorphism.  Imposing these six makes `t` conjugate the
base into a proper subgroup of itself. -/
def stableRelator (i : BaseGenerator) : FreeGroup Generator :=
  stableWord * vertexLetter i * stableWord⁻¹ * (compressedGeneratorWord i)⁻¹

/-- The conjugated lamp `d = t c t⁻¹`.  It is an involution, and it commutes
with the doubling image of the base. -/
abbrev displacedLampWord : FreeGroup Generator :=
  stableWord * lampWord * stableWord⁻¹

/-- The distinguished word `w = [d, v₁ d v₁⁻¹]` with `d = t c t⁻¹`.  Since `d`
is an involution this equals `[d, v₁]²`, so it is a square. -/
abbrev markedWord : FreeGroup Generator :=
  commutatorWord displacedLampWord
    (v1Word * displacedLampWord * v1Word⁻¹)

/-- The twenty base relators, transported into the full alphabet. -/
def transportedBaseRelators : Finset (FreeGroup Generator) :=
  baseRelators.image embedBaseWord

/-- The six stable-letter relators, one for each base letter. -/
def stableRelators : Finset (FreeGroup Generator) :=
  Finset.univ.image stableRelator

/-- The seven lamp relators: `c² = 1`, and `c s = s c` for each of the six base
letters `s`. -/
def lampRelators : Finset (FreeGroup Generator) :=
  {lampWord ^ 2} ∪
    Finset.univ.image (fun i : BaseGenerator ↦
      commutatorWord lampWord (vertexLetter i))

/-- The eight relators making `w` central: `w g = g w` for each of the eight
generators.  Note that `w² = 1` is **not** imposed here; it is a consequence,
proved in the compared theorem. -/
def markedRelators : Finset (FreeGroup Generator) :=
  Finset.univ.image (fun i : Generator ↦
    commutatorWord markedWord (FreeGroup.of i))

/-- All forty-one relators of `E`: twenty base, six stable-letter, seven lamp,
and eight centrality relators. -/
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

/-- **The distinguished element** `w = [t c t⁻¹, v₁ (t c t⁻¹) v₁⁻¹]` of `E`. -/
abbrev w : E := wordInE markedWord

-- END SHARED BLOCK

/-! ## The bridge to the development

These two `rfl`s are the gate.  If the copied block ever drifts from
`GroupApproximation.LiteralNonMFPresentation`, this module stops compiling
instead of silently proving something about a different group. -/

open GroupApproximation

theorem E_eq : E = LiteralNonMFPresentation.MarkedGroup := rfl

theorem w_eq : w = (LiteralNonMFPresentation.mark : E) := rfl

/-! ## The proof -/

/-- **An explicit finitely presented sofic group that is not MF.**

For the group `E` displayed above, on eight generators and forty-one
relators, and its distinguished word `w = [t c t⁻¹, v₁ (t c t⁻¹) v₁⁻¹]`:

1. `E` is finitely presented;
2. `w` is a nontrivial central involution of `E`;
3. six elements generate `E`;
4. `E` is sofic -- it has permutation models in the normalized Hamming
   metric;
5. `E` is hyperlinear -- it has unitary models in the normalized
   Hilbert-Schmidt metric;
6. every operator-norm asymptotic unitary representation of `E` sends `w` to
   the identity, which is exactly the statement that every homomorphism from
   `E` into the unitary group of a matrix quotient kills `w`;
7. uniformly so: one positive defect budget and one finite test set force the
   image of `w` inside the open operator-norm unit ball about the identity,
   in every dimension;
8. consequently `E` is **not** MF: no operator-norm models separate its
   elements;
9. every finite-dimensional linear representation of `E`, over every field,
   also sends `w` to the identity, so none is injective;
10. and so does every homomorphism from `E` to a finite group, so `E` is not
    residually finite.

Clauses 4, 5 and 8 together say that soficity and hyperlinearity do not imply
the MF property.  Clause 2 is what makes 6 to 10 non-vacuous. -/
theorem explicit_fp_sofic_hyperlinear_not_MF :
    Group.IsFinitelyPresented E ∧
    (w ≠ 1 ∧ w ^ 2 = 1 ∧ ∀ g : E, Commute w g) ∧
    (∃ S : Finset E, S.card ≤ 6 ∧ Subgroup.closure (S : Set E) = ⊤) ∧
    IsSoficGroup E ∧
    IsHyperlinearGroup E ∧
    (∀ (Y : ℕ → FiniteCarrier) (U : ∀ n, E → Matrix (Y n) (Y n) ℂ),
        (∀ n g, U n g ∈ Matrix.unitaryGroup (Y n) ℂ) →
        (∀ g h : E, Filter.Tendsto
            (fun n ↦ ‖U n (g * h) - U n g * U n h‖) Filter.atTop (nhds 0)) →
        Filter.Tendsto (fun n ↦ ‖U n w - 1‖) Filter.atTop (nhds 0)) ∧
    (∃ (δ : ℝ) (F₀ : Finset E), 0 < δ ∧
        ∀ (Y : FiniteCarrier) (φ : E → Matrix Y Y ℂ),
          (∀ g, φ g ∈ Matrix.unitaryGroup Y ℂ) →
          (∀ g ∈ F₀, ∀ h ∈ F₀, ‖φ (g * h) - φ g * φ h‖ ≤ δ) →
          ‖φ w - 1‖ < 1) ∧
    ¬ IsMFGroup E ∧
    (∀ (K : Type) (W : Type) [Field K] [AddCommGroup W] [Module K W]
        [FiniteDimensional K W] (π : E →* (Module.End K W)ˣ), π w = 1) ∧
    (∀ (Q : Type) [Group Q] [Finite Q] (φ : E →* Q), φ w = 1) := by
  refine ⟨inferInstance, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact LiteralNonMFLinearWitness.literal_mark_ne_one
  · exact LiteralNonMFPresentation.mark_sq
  · exact LiteralNonMFPresentation.mark_central
  -- six generators: the rank bound, with `rank_spec` turning it into an
  -- explicit generating set
  · obtain ⟨S, hcard, hclosure⟩ :=
      Group.rank_spec LiteralNonMFPresentation.MarkedGroup
    exact ⟨S, hcard.trans_le LiteralSixGenerator.literal_rank_le_six, hclosure⟩
  -- soficity: repackage a `SoficModel` as the bare existential
  · intro F ε hε
    obtain ⟨m⟩ := LiteralSoficAssembly.markedGroup_isSofic F ε hε
    exact ⟨⟨m.carrier.carrier, m.carrier.fintype, m.carrier.decidableEq⟩,
      m.map, m.nonempty, m.multiplicative, m.separated⟩
  -- hyperlinearity: likewise for a `HyperlinearModel`
  · intro F ε hε
    obtain ⟨m⟩ :=
      LiteralSoficAssembly.markedGroup_finitelyPresented_hyperlinear_nonMF.2.1
        F ε hε
    exact ⟨⟨m.carrier.carrier, m.carrier.fintype, m.carrier.decidableEq⟩,
      m.map, m.nonempty, m.isUnitary, m.multiplicative, m.separated⟩
  -- every operator-norm asymptotic representation kills the mark
  · intro Y U hU hmul
    have main : ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ‖U n w - 1‖ < ε := by
      intro ε hε
      obtain ⟨δ, F₀, hδ, hbound⟩ :=
        uniform_invisibility LiteralNonMFEndpoint.literal_mark_normMFInvisible
          ε hε
      have key : ∀ᶠ n in Filter.atTop, ∀ g ∈ F₀, ∀ h ∈ F₀,
          ‖U n (g * h) - U n g * U n h‖ ≤ δ := by
        rw [Filter.eventually_all_finset]
        intro g _
        rw [Filter.eventually_all_finset]
        intro h _
        exact (hmul g h).eventually_le_const hδ
      filter_upwards [key] with n hn
      exact hbound ⟨(Y n).carrier, (Y n).fintype, (Y n).decidableEq⟩
        (fun g ↦ ⟨U n g, hU n g⟩) hn
    refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (main ε hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact hN n hn
  -- the uniform obstruction, repackaged from bundled unitaries to a map
  -- plus a unitarity hypothesis
  · obtain ⟨δ, F₀, hδ, hbound⟩ :=
      LiteralUniformObstruction.literal_uniform_operatorNorm_obstruction
    exact ⟨δ, F₀, hδ, fun Y φ hφ hmul ↦
      hbound ⟨Y.carrier, Y.fintype, Y.decidableEq⟩ (fun g ↦ ⟨φ g, hφ g⟩) hmul⟩
  -- not MF: a local operator-norm model would be a `NormModel` at
  -- separation `1`
  · intro hMF
    refine LiteralNonMFEndpoint.literal_not_isOperatorMF
      (OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mpr
        ?_)
    intro F ε hε
    obtain ⟨Y, V, hpos, hunit, hmul, hsep⟩ := hMF F ε hε
    exact ⟨{ carrier := ⟨Y.carrier, Y.fintype, Y.decidableEq⟩
             nonempty := hpos
             map := V
             isUnitary := hunit
             multiplicative := hmul
             separated := hsep }⟩
  -- every finite-dimensional representation over every field kills the mark
  -- the universes are pinned explicitly: the third one belongs to the
  -- finite-quotient clause, which this bullet does not use, so inference has
  -- nothing to determine it from.
  · intro K W _ _ _ _ π
    exact
      LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences.{0,
        0, 0}.2.1 π
  -- every finite quotient kills the mark, which is the third clause of the
  -- same finite-dimensional endpoint
  · intro Q _ _ φ
    exact
      LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences.{0,
        0, 0}.2.2 φ

/-! ## Axiom closure

The registry permits exactly `propext`, `Quot.sound` and `Classical.choice`,
and Comparator enforces that on the exported proof.  `#audit_axioms` enforces
the same thing here, at build time: it prints the report and then throws
unless the closure is classical, so a submission can never be prepared
against a tree in which this theorem has silently acquired another axiom. -/

#audit_axioms ExplicitNonMF.explicit_fp_sofic_hyperlinear_not_MF

end

end ExplicitNonMF
