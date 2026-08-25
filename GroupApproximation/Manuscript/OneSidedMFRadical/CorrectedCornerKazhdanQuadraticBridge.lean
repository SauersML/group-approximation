import GroupApproximation.Manuscript.OneSidedMFRadical.UnconditionalCornerTraceAssembly
import GroupApproximation.Analysis.MaximalCStarKazhdanProjection

/-!
# From the corrected corner Kazhdan representation to its Gram lower bound

This file replaces the quadratic-form premise of
`eventually_correctedCorner_trace_inequality` by the unchanged manuscript's
actual representation-theoretic input.  The corrected maps define an omega
representation, the faithful universal GNS map turns it into a unitary
Hilbert-space representation, and the complex Kazhdan inequality gives the
lower bound for its Gram operator.

The remaining datum is stated at its exact algebraic location: the maximal
Kazhdan projection maps to zero in this corrected corner representation.  It
implies that the represented corner has no nonzero invariant vector by the
already formalized fixed-vector characterization of the Kazhdan projection.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix PrintedCornerCompression
open AbstractSpectralGap OmegaCoronaKazhdanProjection
open VectorOmegaAction UnitaryAverageFixedVector
open GNSEigenvector MaximalCStarKazhdanProjection
open UltraproductKazhdanProjection
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G]
variable {model : ℕ → FiniteModel}

/-- The bounded-operator algebra of the concrete faithful corner-corona
representation.  Naming it keeps the representation-theoretic statements
small enough to elaborate without repeatedly normalizing the universal GNS
space. -/
abbrev CorrectedCornerOperatorAlgebra (D : PrintedCornerData G model)
    (ω : Ultrafilter ℕ) :=
  CorrectedCornerFaithfulSpace D ω →L[ℂ] CorrectedCornerFaithfulSpace D ω

/-- The actual polar-corrected corner maps as an omega-multiplicative family.
The only filter input is that `ω` refines `cofinite`; the corrected defects
already tend to zero at `atTop = cofinite`. -/
noncomputable def correctedCornerOmegaRepresentation
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    OmegaUnitaryRep (fun n ↦ D.cornerModel n) ω G where
  V n g := D.cornerMap n g
  mul_null := by
    intro g h
    have hωtop : (ω : Filter ℕ) ≤ atTop := by
      simpa [Nat.cofinite_eq_atTop] using hω
    rw [IsNullMatrixSequence]
    simpa only [unitarySeq_apply, lp.coeFn_sub, Pi.sub_apply,
      lp.infty_coeFn_mul, Pi.mul_apply] using
      (D.cornerMap_mul_defect_tendsto g h).mono_left hωtop

/-- The corrected corner representation after applying the fixed faithful
universal GNS representation, still bundled as operator unitaries. -/
noncomputable def correctedCornerOperatorUnitaryRepresentation
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    G →* unitary (CorrectedCornerOperatorAlgebra D ω) :=
  (unitaryMap (cornerCoronaFaithfulRepresentation
      (fun n ↦ D.cornerModel n) ω)).comp
    (coronaRep (fun n ↦ D.cornerModel n) ω
      (correctedCornerOmegaRepresentation D ω hω))

/-- The operator underlying the corrected-corner unitary at a group element. -/
noncomputable def correctedCornerOperator
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (g : G) :
    CorrectedCornerOperatorAlgebra D ω :=
  (correctedCornerOperatorUnitaryRepresentation D ω hω g :
    CorrectedCornerOperatorAlgebra D ω)

/-- The same actual representation in the format consumed by the complex
Kazhdan inequality. -/
noncomputable def correctedCornerHilbertRepresentation
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    G →* (CorrectedCornerFaithfulSpace D ω ≃ₗᵢ[ℂ]
      CorrectedCornerFaithfulSpace D ω) :=
  unitaryIsometryHom.comp
    (correctedCornerOperatorUnitaryRepresentation D ω hω)

/-- The represented Gram class is exactly the sum of the displacement
operators of the actual corrected-corner representation. -/
theorem correctedCornerGramOperator_eq_displacementSum
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (S : Finset G) :
    correctedCornerGramOperator D ω S =
      ∑ s ∈ S,
        star (correctedCornerOperator D ω hω s - 1) *
          (correctedCornerOperator D ω hω s - 1) := by
  let Phi : BoundedMatrixSequence (fun n ↦ D.cornerModel n) →⋆ₐ[ℂ]
      CorrectedCornerOperatorAlgebra D ω :=
    (cornerCoronaFaithfulRepresentation (fun n ↦ D.cornerModel n) ω).comp
      (filterMatrixCStarCoronaQuotient
        (fun n ↦ D.cornerModel n) (ω : Filter ℕ))
  change Phi (∑ s ∈ S,
      star (correctedCornerMapSequence D s - 1) *
        (correctedCornerMapSequence D s - 1)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [map_mul, map_star, map_sub, map_one]
  rfl

/-- The quadratic form of the fixed Gram operator is the sum of squared
displacements in the actual corrected-corner Hilbert representation. -/
theorem re_inner_correctedCornerGramOperator
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (S : Finset G)
    (x : CorrectedCornerFaithfulSpace D ω) :
    (⟪x, correctedCornerGramOperator D ω S x⟫_ℂ).re =
      ∑ s ∈ S,
        ‖correctedCornerHilbertRepresentation D ω hω s x - x‖ ^ 2 := by
  rw [correctedCornerGramOperator_eq_displacementSum D ω hω S,
    _root_.sum_apply, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact CStarTensor.re_inner_self _

/-- The precise remaining algebraic input from the unchanged complement-
projection construction: the maximal Kazhdan projection has zero image in the
actual corrected corner representation. -/
def CorrectedCornerKazhdanProjectionZero
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (K : KazhdanData G) : Prop :=
  ∀ f : MaximalGroupCStar G →⋆ₐ[ℂ]
      CorrectedCornerOperatorAlgebra D ω,
    (∀ g : G, f (maximalGroupCStarGenerator G g) =
      correctedCornerOperator D ω hω g) →
    f K.projection = 0

/-- The maximal Kazhdan projection has its fixed-vector characterization on
the concrete (small-universe) universal GNS space.  `KazhdanData.kazhdan` is
stored one universe higher because it constructs `Cmax(G)`; the repository's
universe-descent theorem supplies the same pair at this Hilbert-space
universe. -/
theorem correctedCornerMaximalProjectionImageIsFixedProjection
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (K : KazhdanData G) :
    ∃ f : MaximalGroupCStar G →⋆ₐ[ℂ]
        CorrectedCornerOperatorAlgebra D ω,
      (∀ g : G, f (maximalGroupCStarGenerator G g) =
        correctedCornerOperator D ω hω g) ∧
      ∀ x : CorrectedCornerFaithfulSpace D ω,
        f K.projection x = x ↔
          ∀ g : G,
            correctedCornerOperator D ω hω g x = x := by
  let rho := correctedCornerOperatorUnitaryRepresentation D ω hω
  obtain ⟨f, hf, _hunique⟩ :=
    maximalGroupCStar_existsUnique_lift_allUniverses G rho
  refine ⟨f, hf, ?_⟩
  have hgap : ∀ mu ∈ spectrum ℝ (unitaryAverage rho K.S),
      mu ≤ K.rate ∨ mu = 1 := by
    intro mu hmu
    by_cases hmu1 : mu = 1
    · exact Or.inr hmu1
    · left
      have hmuC : (mu : ℂ) ∈ spectrum ℂ (unitaryAverage rho K.S) := by
        have h := spectrum.algebraMap_mem ℂ hmu
        rwa [show (algebraMap ℝ ℂ) mu = (mu : ℂ) by simp] at h
      exact unitaryAverage_spectrum_le_manuscript rho
        K.kazhdan.lowerUniverse K.S Finset.Subset.rfl K.one_mem K.symm
          hmuC hmu1
  have himage : f K.projection =
      CStarSpectralProjection.spectralProjection
        (unitaryAverage rho K.S) K.rate :=
    image_eq_spectralProjection K rho f hf hgap
  intro x
  rw [himage, spectralProjection_apply_eq_self_iff rho
    ⟨1, K.one_mem⟩ K.symm K.rate_lt_one hgap x]
  constructor
  · intro h g
    apply apply_eq_self_of_mem_closure rho (fun s hs ↦ h s hs)
    rw [K.generates]
    trivial
  · intro h s _hs
    exact h s

/-- Vanishing of the corner Kazhdan projection rules out nonzero invariant
vectors in the actual corrected-corner Hilbert representation. -/
theorem correctedCornerHilbertRepresentation_hasNoInvariantVectors
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (K : KazhdanData G)
    (hzero : CorrectedCornerKazhdanProjectionZero D ω hω K) :
    ∀ x : CorrectedCornerFaithfulSpace D ω,
      (∀ g : G, correctedCornerHilbertRepresentation D ω hω g x = x) →
      x = 0 := by
  obtain ⟨f, hf, hfix⟩ :=
    correctedCornerMaximalProjectionImageIsFixedProjection D ω hω K
  have hpzero : f K.projection = 0 := hzero f hf
  intro x hx
  have hpx : f K.projection x = x := (hfix x).2 (fun g ↦ hx g)
  rw [hpzero] at hpx
  simpa using hpx.symm

/-- The final former `hquad` premise, derived from the actual corrected-corner
representation, its zero Kazhdan projection, and the Kazhdan inequality. -/
theorem correctedCorner_kazhdan_quadraticForm
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (K : KazhdanData G)
    (hzero : CorrectedCornerKazhdanProjectionZero D ω hω K)
    (x : CorrectedCornerFaithfulSpace D ω) :
    K.kappa ^ 2 * ‖x‖ ^ 2 ≤
      (⟪x, correctedCornerGramOperator D ω K.S x⟫_ℂ).re := by
  rw [re_inner_correctedCornerGramOperator D ω hω K.S x]
  exact complex_kazhdan_sum_sq_ge_of_noInvariant K.kazhdan.lowerUniverse
    (correctedCornerHilbertRepresentation D ω hω)
    (correctedCornerHilbertRepresentation_hasNoInvariantVectors
      D ω hω K hzero) x

/-- **Corner trace inequality with no quadratic-form premise.**  The result is
now driven by the actual corrected maps, the actual faithful universal GNS
representation, and the unchanged Kazhdan projection argument. -/
theorem eventually_correctedCorner_trace_inequality_of_projectionZero
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (K : KazhdanData G)
    (hzero : CorrectedCornerKazhdanProjectionZero D ω hω K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in (ω : Filter ℕ),
      (K.kappa ^ 2 - epsilon) / K.S.card ≤
        (K.S.card : ℝ)⁻¹ * ∑ s ∈ K.S,
          hsNormSq (D.cornerModel n)
            ((D.cornerMap n s :
              Matrix (D.cornerModel n) (D.cornerModel n) ℂ) - 1) :=
  eventually_correctedCorner_trace_inequality D ω K.S (K.kappa ^ 2)
    (correctedCorner_kazhdan_quadraticForm D ω hω K hzero) hepsilon

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
