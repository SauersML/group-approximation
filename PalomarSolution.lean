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
import GroupApproximation.Meta.AxiomGuard

/-!
# Proof of the advertised statement

The declaration block and theorem type match `Palomar/Challenge.lean`.
`E_eq` and `w_eq` definitionally pin the copied presentation to the
development; submission gates check source identity and elaborated closure.
-/

namespace ExplicitNonMF

open scoped Matrix.Norms.L2Operator

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical with `PalomarSolution.lean`)

/-- A finite index type for matrix and permutation models. -/
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

/-- The squared normalized Hilbert--Schmidt distance between two matrices. -/
def hsDistSq (Y : FiniteCarrier) (A B : Matrix Y Y ℂ) : ℝ :=
  (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)) / Fintype.card Y

/-- Soficity in the finite-set normalized-Hamming formulation. -/
def IsSoficGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (σ : G → Equiv.Perm Y),
      0 < Fintype.card Y ∧
      (∀ g ∈ F, ∀ h ∈ F, hammingDist Y (σ (g * h)) (σ g * σ h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 1 - ε ≤ hammingDist Y (σ g) (σ h))

/-- Hyperlinearity in the finite-set normalized-Hilbert--Schmidt formulation. -/
def IsHyperlinearGroup (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteCarrier) (U : G → Matrix Y Y ℂ),
      0 < Fintype.card Y ∧
      (∀ g, U g ∈ Matrix.unitaryGroup Y ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, hsDistSq Y (U (g * h)) (U g * U h) ≤ ε) ∧
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → 2 - ε ≤ hsDistSq Y (U g) (U h))

/-- The sequential operator-norm form of the CDE matrix-corona MF property. -/
def IsSequentialOperatorMFGroup (G : Type) [Group G] : Prop :=
  ∃ (Y : ℕ → FiniteCarrier) (U : ∀ n, G → Matrix (Y n) (Y n) ℂ),
    (∀ n, 0 < Fintype.card (Y n)) ∧
    (∀ n g, U n g ∈ Matrix.unitaryGroup (Y n) ℂ) ∧
    (∀ g h : G, Filter.Tendsto
      (fun n ↦ ‖U n (g * h) - U n g * U n h‖) Filter.atTop (nhds 0)) ∧
    (∀ g : G, g ≠ 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in Filter.atTop, δ ≤ ‖U n g - 1‖)

local instance literalDecidableEq {α : Type*} : DecidableEq α :=
  Classical.decEq α

/-- The six base letters. -/
abbrev BaseGenerator := Fin 6

/-- The six base letters followed by `t` and `c`. -/
abbrev Generator := BaseGenerator ⊕ Fin 2

/-- Index of `v₁`. -/ abbrev v1Index : BaseGenerator := 0
/-- Index of `v₂`. -/ abbrev v2Index : BaseGenerator := 1
/-- Index of `v₃`. -/ abbrev v3Index : BaseGenerator := 2
/-- Index of `x`. -/ abbrev xIndex : BaseGenerator := 3
/-- Index of `y`. -/ abbrev yIndex : BaseGenerator := 4
/-- Index of `z`. -/ abbrev zIndex : BaseGenerator := 5

/-- A base letter in the full alphabet. -/
abbrev Generator.base (i : BaseGenerator) : Generator := Sum.inl i
/-- The stable letter `t`. -/ abbrev Generator.stable : Generator := Sum.inr 0
/-- The lamp letter `c`. -/ abbrev Generator.lamp : Generator := Sum.inr 1

/-- The base word `v₁`. -/ abbrev bv1 : FreeGroup BaseGenerator := FreeGroup.of v1Index
/-- The base word `v₂`. -/ abbrev bv2 : FreeGroup BaseGenerator := FreeGroup.of v2Index
/-- The base word `v₃`. -/ abbrev bv3 : FreeGroup BaseGenerator := FreeGroup.of v3Index
/-- The base word `x`. -/ abbrev bx : FreeGroup BaseGenerator := FreeGroup.of xIndex
/-- The base word `y`. -/ abbrev bY : FreeGroup BaseGenerator := FreeGroup.of yIndex
/-- The base word `z`. -/ abbrev bz : FreeGroup BaseGenerator := FreeGroup.of zIndex

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

/-- The word `[g,h] = g h g⁻¹ h⁻¹`. -/
def commutatorWord {G : Type*} [Group G] (g h : G) : G :=
  g * h * g⁻¹ * h⁻¹

/-- Embed a word in the six base letters into the full alphabet. -/
def embedBaseWord : FreeGroup BaseGenerator →* FreeGroup Generator :=
  FreeGroup.lift fun i ↦ vertexLetter i

/-! The twenty affine-base relators. -/

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
/-- `(x y)⁶ = 1`. -/
abbrev baseRelXYSix : FreeGroup BaseGenerator := (bx * bY) ^ 6

/-- `v₁ v₂ = v₂ v₁`. -/
abbrev baseRelV12 : FreeGroup BaseGenerator := commutatorWord bv1 bv2
/-- `v₁ v₃ = v₃ v₁`. -/
abbrev baseRelV13 : FreeGroup BaseGenerator := commutatorWord bv1 bv3
/-- `v₂ v₃ = v₃ v₂`. -/
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

/-! The remaining twenty-one relators. -/

/-- Doubles translations and fixes the linear generators. -/
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

/-- The relator `t s t⁻¹ = α(s)`. -/
def stableRelator (i : BaseGenerator) : FreeGroup Generator :=
  stableWord * vertexLetter i * stableWord⁻¹ * (compressedGeneratorWord i)⁻¹

/-- The word `d = t c t⁻¹`. -/
abbrev displacedLampWord : FreeGroup Generator :=
  stableWord * lampWord * stableWord⁻¹

/-- The word `w = [d, v₁ d v₁⁻¹]`. -/
abbrev markedWord : FreeGroup Generator :=
  commutatorWord displacedLampWord
    (v1Word * displacedLampWord * v1Word⁻¹)

/-- The twenty base relators, transported into the full alphabet. -/
def transportedBaseRelators : Finset (FreeGroup Generator) :=
  baseRelators.image embedBaseWord

/-- The six stable-letter relators, one for each base letter. -/
def stableRelators : Finset (FreeGroup Generator) :=
  Finset.univ.image stableRelator

/-- The relators `c²=1` and `[c,s]=1` for the six base letters. -/
def lampRelators : Finset (FreeGroup Generator) :=
  {lampWord ^ 2} ∪
    Finset.univ.image (fun i : BaseGenerator ↦
      commutatorWord lampWord (vertexLetter i))

/-- The eight relators making `w` central. -/
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

/-! ## Bridge to the development -/

open GroupApproximation

theorem E_eq : E = LiteralNonMFPresentation.MarkedGroup := rfl

theorem w_eq : w = (LiteralNonMFPresentation.mark : E) := rfl

/-- The literal group has the displayed finiteness, approximation and
representation properties. -/
theorem explicit_fp_sofic_hyperlinear_not_MF :
    Fintype.card Generator = 8 ∧
    relators.card = 41 ∧
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
    ¬ IsSequentialOperatorMFGroup E ∧
    (∀ (K : Type) (W : Type) [Field K] [AddCommGroup W] [Module K W]
        [FiniteDimensional K W] (π : E →* (Module.End K W)ˣ), π w = 1) ∧
    (∀ (Q : Type) [Group Q] [Finite Q] (φ : E →* Q), φ w = 1) := by
  refine ⟨?_, ?_, inferInstance, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact LiteralNonMFPresentation.generator_card
  · exact LiteralNonMFPresentation.relators_card
  · exact LiteralNonMFLinearWitness.literal_mark_ne_one
  · exact LiteralNonMFPresentation.mark_sq
  · exact LiteralNonMFPresentation.mark_central
  · obtain ⟨S, hcard, hclosure⟩ :=
      Group.rank_spec LiteralNonMFPresentation.MarkedGroup
    exact ⟨S, hcard.trans_le LiteralSixGenerator.literal_rank_le_six, hclosure⟩
  · intro F ε hε
    obtain ⟨m⟩ := LiteralSoficAssembly.markedGroup_isSofic F ε hε
    exact ⟨⟨m.carrier.carrier, m.carrier.fintype, m.carrier.decidableEq⟩,
      m.map, m.nonempty, m.multiplicative, m.separated⟩
  · intro F ε hε
    obtain ⟨m⟩ :=
      LiteralSoficAssembly.markedGroup_finitelyPresented_hyperlinear_nonMF.2.1
        F ε hε
    exact ⟨⟨m.carrier.carrier, m.carrier.fintype, m.carrier.decidableEq⟩,
      m.map, m.nonempty, m.isUnitary, m.multiplicative, m.separated⟩
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
  · obtain ⟨δ, F₀, hδ, hbound⟩ :=
      LiteralUniformObstruction.literal_uniform_operatorNorm_obstruction
    exact ⟨δ, F₀, hδ, fun Y φ hφ hmul ↦
      hbound ⟨Y.carrier, Y.fintype, Y.decidableEq⟩ (fun g ↦ ⟨φ g, hφ g⟩) hmul⟩
  · rintro ⟨Y, U, _, hU, hmul, hsep⟩
    have hzero : Filter.Tendsto (fun n ↦ ‖U n w - 1‖)
        Filter.atTop (nhds 0) := by
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
    obtain ⟨δ, hδ, hgap⟩ :=
      hsep w LiteralNonMFLinearWitness.literal_mark_ne_one
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hzero δ hδ
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hgap
    let n := max N M
    have hnear := hN n (le_max_left N M)
    have hfar := hM n (le_max_right N M)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hnear
    exact (not_lt_of_ge hfar) hnear
  -- Explicit universes include the later finite-quotient clause's universe.
  · intro K W _ _ _ _ π
    exact
      LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences.{0,
        0, 0}.2.1 π
  · intro Q _ _ φ
    exact
      LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences.{0,
        0, 0}.2.2 φ

/-! The selected theorem uses only the permitted classical axioms. -/

#audit_axioms ExplicitNonMF.explicit_fp_sofic_hyperlinear_not_MF

end

end ExplicitNonMF
