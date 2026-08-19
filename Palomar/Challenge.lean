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
# TODO: title

TODO: the mathematical account of this statement.  Palomar's editorial
review reads this against the Lean, so it must say what is claimed, how the
MF property is formalized here, and where the result came from.
-/

namespace ExplicitNonMF

open scoped Matrix.Norms.L2Operator

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical with `Palomar/Solution.lean`)

/-! ## TODO: section heading -/

/-- TODO: docstring for `FiniteCarrier`. -/
structure FiniteCarrier where
  /-- TODO: docstring for this declaration. -/
  carrier : Type
  /-- TODO: docstring for this declaration. -/
  fintype : Fintype carrier
  /-- TODO: docstring for this declaration. -/
  decidableEq : DecidableEq carrier

instance finiteCarrierCoeSort : CoeSort FiniteCarrier Type :=
  ⟨FiniteCarrier.carrier⟩

@[reducible, instance] def finiteCarrierFintype (Y : FiniteCarrier) :
    Fintype Y :=
  Y.fintype

@[reducible, instance] def finiteCarrierDecidableEq (Y : FiniteCarrier) :
    DecidableEq Y :=
  Y.decidableEq

/-! ## TODO: section heading -/

/-- TODO: docstring for `hammingDist`. -/
def hammingDist (Y : FiniteCarrier) (p q : Equiv.Perm Y) : ℝ :=
  ((Finset.univ.filter fun y : Y ↦ p y ≠ q y).card : ℝ) / Fintype.card Y

/-- TODO: docstring for `hsDistSq`. -/
def hsDistSq (Y : FiniteCarrier) (A B : Matrix Y Y ℂ) : ℝ :=
  (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)) / Fintype.card Y

/-- TODO: docstring for `IsSoficGroup`. -/
def IsSoficGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (σ : G → Equiv.Perm Y),
      0 < Fintype.card Y ∧
      (∀ g ∈ F, ∀ h ∈ F, hammingDist Y (σ (g * h)) (σ g * σ h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 1 - ε ≤ hammingDist Y (σ g) (σ h))

/-- TODO: docstring for `IsHyperlinearGroup`. -/
def IsHyperlinearGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (U : G → Matrix Y Y ℂ),
      0 < Fintype.card Y ∧
      (∀ g, U g ∈ Matrix.unitaryGroup Y ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, hsDistSq Y (U (g * h)) (U g * U h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 2 - ε ≤ hsDistSq Y (U g) (U h))

/-- TODO: docstring for `IsMFGroup`. -/
def IsMFGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (U : G → Matrix Y Y ℂ),
      0 < Fintype.card Y ∧
      (∀ g, U g ∈ Matrix.unitaryGroup Y ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, ‖U (g * h) - U g * U h‖ ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 1 ≤ ‖U g - U h‖)

/-! ## TODO: section heading -/

/-- TODO: docstring for `literalDecidableEq`. -/
local instance literalDecidableEq {α : Type*} : DecidableEq α :=
  Classical.decEq α

/-- TODO: docstring for `BaseGenerator`. -/
abbrev BaseGenerator := Fin 6

/-- TODO: docstring for `Generator`. -/
abbrev Generator := BaseGenerator ⊕ Fin 2

/-- TODO: docstring for `v1Index`. -/
abbrev v1Index : BaseGenerator := 0
/-- TODO: docstring for `v2Index`. -/
abbrev v2Index : BaseGenerator := 1
/-- TODO: docstring for `v3Index`. -/
abbrev v3Index : BaseGenerator := 2
/-- TODO: docstring for `xIndex`. -/
abbrev xIndex : BaseGenerator := 3
/-- TODO: docstring for `yIndex`. -/
abbrev yIndex : BaseGenerator := 4
/-- TODO: docstring for `zIndex`. -/
abbrev zIndex : BaseGenerator := 5

/-- TODO: docstring for `Generator.base`. -/
abbrev Generator.base (i : BaseGenerator) : Generator := Sum.inl i
/-- TODO: docstring for `Generator.stable`. -/
abbrev Generator.stable : Generator := Sum.inr 0
/-- TODO: docstring for `Generator.lamp`. -/
abbrev Generator.lamp : Generator := Sum.inr 1

/-- TODO: docstring for `bv1`. -/
abbrev bv1 : FreeGroup BaseGenerator := FreeGroup.of v1Index
/-- TODO: docstring for `bv2`. -/
abbrev bv2 : FreeGroup BaseGenerator := FreeGroup.of v2Index
/-- TODO: docstring for `bv3`. -/
abbrev bv3 : FreeGroup BaseGenerator := FreeGroup.of v3Index
/-- TODO: docstring for `bx`. -/
abbrev bx : FreeGroup BaseGenerator := FreeGroup.of xIndex
/-- TODO: docstring for `bY`. -/
abbrev bY : FreeGroup BaseGenerator := FreeGroup.of yIndex
/-- TODO: docstring for `bz`. -/
abbrev bz : FreeGroup BaseGenerator := FreeGroup.of zIndex

/-- TODO: docstring for `vertexLetter`. -/
abbrev vertexLetter (i : BaseGenerator) : FreeGroup Generator :=
  FreeGroup.of (Generator.base i)

/-- TODO: docstring for `v1Word`. -/
abbrev v1Word : FreeGroup Generator := vertexLetter v1Index
/-- TODO: docstring for `v2Word`. -/
abbrev v2Word : FreeGroup Generator := vertexLetter v2Index
/-- TODO: docstring for `v3Word`. -/
abbrev v3Word : FreeGroup Generator := vertexLetter v3Index
/-- TODO: docstring for `xWord`. -/
abbrev xWord : FreeGroup Generator := vertexLetter xIndex
/-- TODO: docstring for `yWord`. -/
abbrev yWord : FreeGroup Generator := vertexLetter yIndex
/-- TODO: docstring for `zWord`. -/
abbrev zWord : FreeGroup Generator := vertexLetter zIndex
/-- TODO: docstring for `stableWord`. -/
abbrev stableWord : FreeGroup Generator := FreeGroup.of Generator.stable
/-- TODO: docstring for `lampWord`. -/
abbrev lampWord : FreeGroup Generator := FreeGroup.of Generator.lamp

/-- TODO: docstring for `commutatorWord`. -/
def commutatorWord {G : Type*} [Group G] (g h : G) : G :=
  g * h * g⁻¹ * h⁻¹

/-- TODO: docstring for `embedBaseWord`. -/
def embedBaseWord : FreeGroup BaseGenerator →* FreeGroup Generator :=
  FreeGroup.lift fun i ↦ vertexLetter i

/-! ## TODO: section heading -/

/-- TODO: docstring for `baseRelXCube`. -/
abbrev baseRelXCube : FreeGroup BaseGenerator := bx ^ 3
/-- TODO: docstring for `baseRelYCube`. -/
abbrev baseRelYCube : FreeGroup BaseGenerator := bY ^ 3
/-- TODO: docstring for `baseRelZSq`. -/
abbrev baseRelZSq : FreeGroup BaseGenerator := bz ^ 2
/-- TODO: docstring for `baseRelXZCube`. -/
abbrev baseRelXZCube : FreeGroup BaseGenerator := (bx * bz) ^ 3
/-- TODO: docstring for `baseRelYZCube`. -/
abbrev baseRelYZCube : FreeGroup BaseGenerator := (bY * bz) ^ 3
/-- TODO: docstring for `baseRelXInvZXY`. -/
abbrev baseRelXInvZXY : FreeGroup BaseGenerator := (bx⁻¹ * bz * bx * bY) ^ 2
/-- TODO: docstring for `baseRelYInvZYX`. -/
abbrev baseRelYInvZYX : FreeGroup BaseGenerator := (bY⁻¹ * bz * bY * bx) ^ 2
/-- TODO: docstring for `baseRelXYSix`. -/
abbrev baseRelXYSix : FreeGroup BaseGenerator := (bx * bY) ^ 6

/-- TODO: docstring for `baseRelV12`. -/
abbrev baseRelV12 : FreeGroup BaseGenerator := commutatorWord bv1 bv2
/-- TODO: docstring for `baseRelV13`. -/
abbrev baseRelV13 : FreeGroup BaseGenerator := commutatorWord bv1 bv3
/-- TODO: docstring for `baseRelV23`. -/
abbrev baseRelV23 : FreeGroup BaseGenerator := commutatorWord bv2 bv3

/-- TODO: docstring for `baseRelXV1`. -/
abbrev baseRelXV1 : FreeGroup BaseGenerator := bx * bv1 * bx⁻¹ * bv3⁻¹
/-- TODO: docstring for `baseRelXV2`. -/
abbrev baseRelXV2 : FreeGroup BaseGenerator := bx * bv2 * bx⁻¹ * bv1⁻¹
/-- TODO: docstring for `baseRelXV3`. -/
abbrev baseRelXV3 : FreeGroup BaseGenerator := bx * bv3 * bx⁻¹ * bv2⁻¹
/-- TODO: docstring for `baseRelYV1`. -/
abbrev baseRelYV1 : FreeGroup BaseGenerator := bY * bv1 * bY⁻¹ * bv1⁻¹
/-- TODO: docstring for `baseRelYV2`. -/
abbrev baseRelYV2 : FreeGroup BaseGenerator :=
  bY * bv2 * bY⁻¹ * (bv2⁻¹ * bv3)⁻¹
/-- TODO: docstring for `baseRelYV3`. -/
abbrev baseRelYV3 : FreeGroup BaseGenerator :=
  bY * bv3 * bY⁻¹ * (bv1 * bv2⁻¹)⁻¹
/-- TODO: docstring for `baseRelZV1`. -/
abbrev baseRelZV1 : FreeGroup BaseGenerator :=
  bz * bv1 * bz⁻¹ * (bv2 * bv3⁻¹)⁻¹
/-- TODO: docstring for `baseRelZV2`. -/
abbrev baseRelZV2 : FreeGroup BaseGenerator :=
  bz * bv2 * bz⁻¹ * (bv1 * bv3⁻¹)⁻¹
/-- TODO: docstring for `baseRelZV3`. -/
abbrev baseRelZV3 : FreeGroup BaseGenerator :=
  bz * bv3 * bz⁻¹ * (bv3⁻¹)⁻¹

/-- TODO: docstring for `baseRelators`. -/
def baseRelators : Finset (FreeGroup BaseGenerator) :=
  [baseRelXCube, baseRelYCube, baseRelZSq, baseRelXZCube,
   baseRelYZCube, baseRelXInvZXY, baseRelYInvZYX, baseRelXYSix,
   baseRelV12, baseRelV13, baseRelV23,
   baseRelXV1, baseRelXV2, baseRelXV3,
   baseRelYV1, baseRelYV2, baseRelYV3,
   baseRelZV1, baseRelZV2, baseRelZV3].toFinset

/-! ## TODO: section heading -/

/-- TODO: docstring for `compressedBaseWord`. -/
def compressedBaseWord (i : BaseGenerator) : FreeGroup BaseGenerator :=
  if i = v1Index then bv1 ^ 2
  else if i = v2Index then bv2 ^ 2
  else if i = v3Index then bv3 ^ 2
  else if i = xIndex then bx
  else if i = yIndex then bY
  else bz

/-- TODO: docstring for `compressedGeneratorWord`. -/
def compressedGeneratorWord (i : BaseGenerator) : FreeGroup Generator :=
  embedBaseWord (compressedBaseWord i)

/-- TODO: docstring for `stableRelator`. -/
def stableRelator (i : BaseGenerator) : FreeGroup Generator :=
  stableWord * vertexLetter i * stableWord⁻¹ * (compressedGeneratorWord i)⁻¹

/-- TODO: docstring for `displacedLampWord`. -/
abbrev displacedLampWord : FreeGroup Generator :=
  stableWord * lampWord * stableWord⁻¹

/-- TODO: docstring for `markedWord`. -/
abbrev markedWord : FreeGroup Generator :=
  commutatorWord displacedLampWord
    (v1Word * displacedLampWord * v1Word⁻¹)

/-- TODO: docstring for `transportedBaseRelators`. -/
def transportedBaseRelators : Finset (FreeGroup Generator) :=
  baseRelators.image embedBaseWord

/-- TODO: docstring for `stableRelators`. -/
def stableRelators : Finset (FreeGroup Generator) :=
  Finset.univ.image stableRelator

/-- TODO: docstring for `lampRelators`. -/
def lampRelators : Finset (FreeGroup Generator) :=
  {lampWord ^ 2} ∪
    Finset.univ.image (fun i : BaseGenerator ↦
      commutatorWord lampWord (vertexLetter i))

/-- TODO: docstring for `markedRelators`. -/
def markedRelators : Finset (FreeGroup Generator) :=
  Finset.univ.image (fun i : Generator ↦
    commutatorWord markedWord (FreeGroup.of i))

/-- TODO: docstring for `relators`. -/
def relators : Finset (FreeGroup Generator) :=
  transportedBaseRelators ∪ stableRelators ∪ lampRelators ∪ markedRelators

/-- TODO: docstring for `E`. -/
abbrev E : Type :=
  PresentedGroup ((relators : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

/-- TODO: docstring for `wordInE`. -/
abbrev wordInE : FreeGroup Generator →* E :=
  PresentedGroup.mk ((relators : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

/-- TODO: docstring for `w`. -/
abbrev w : E := wordInE markedWord

-- END SHARED BLOCK

/-! ## TODO: section heading -/

/-- TODO: docstring for `explicit_fp_sofic_hyperlinear_not_MF`. -/
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
  sorry

end

end ExplicitNonMF
