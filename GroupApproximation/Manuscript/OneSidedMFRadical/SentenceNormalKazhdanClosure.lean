import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoordinatePassage
import GroupApproximation.Analysis.MaximalCStarKazhdanProjection
import GroupApproximation.Analysis.UnitaryAverageFixedVector
import GroupApproximation.Sofic.KazhdanCompressionFunctorial
import GroupApproximation.Sofic.CornerDilutionInvariance

/-!
# Original normal-Kazhdan proof: sentence-level declarations

This file does not replace the printed corner proof by the moving-corner
endpoint.  It names the unconditional pieces of the original
faithful-representation, Kazhdan-corner, and normalized-coordinate-trace route.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open AbstractSpectralGap
open MaximalCStarKazhdanProjection
open UnitaryAverageFixedVector
open UltraproductKazhdanProjection
open scoped Matrix.Norms.L2Operator

universe u

/-- Row 155: a finite matrix corner is normalized by its own dimension, not
the dimension of a containing padded matrix algebra. -/
theorem manuscriptSentence155_cornerOwnNormalizedTrace
    (Y : FiniteModel) (m : ℕ) (A : Matrix Y Y ℂ) :
    normTrace Y A =
      Matrix.trace
          (CornerDilutionInvariance.cornerProj Y m *
            padMatrix Y m A *
            CornerDilutionInvariance.cornerProj Y m) /
        (Fintype.card Y : ℂ) :=
  CornerDilutionInvariance.normTrace_corner_eq Y m A

/-- Row 156: on the complementary fixed-vector sector, the Kazhdan inequality
detects every nonzero vector with the printed constant. -/
theorem manuscriptSentence156_cornerKazhdanDetection
    {K : Type u} [Group K] {S : Finset K} {kappa : ℝ}
    (hS : IsKazhdanPair.{u, u} K S kappa)
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (rho : K →* (E ≃ₗᵢ[ℂ] E)) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    ∀ x : (KazhdanOrthogonal.invariantSubmodule (realifyHom rho))ᗮ,
      kappa ^ 2 / S.card * ‖x‖ ^ 2 ≤
        (S.card : ℝ)⁻¹ * ∑ s ∈ S,
          ‖KazhdanOrthogonal.orthogonalRepresentation (realifyHom rho) s x - x‖ ^ 2 := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  intro x
  exact corner_kazhdan_average_sq_ge hS (realifyHom rho) x

/-- Row 169: passage to a quotient image preserves normality and property
`(T)`; survival of one element makes the image subgroup nontrivial. -/
theorem manuscriptSentence169_quotientImageRetainsNormalKazhdan
    {G H : Type} [Group G] [Group H]
    (K : Subgroup G) [K.Normal] (hT : HasKazhdanPropertyT.{0, 0} K)
    (f : G →* H) (hf : Function.Surjective f) {k : G}
    (hk : k ∈ K) (hsurvive : f k ≠ 1) :
    (K.map f).Normal ∧ HasKazhdanPropertyT.{0, 0} (K.map f) ∧
      Nontrivial (K.map f) := by
  have hnormal : (K.map f).Normal :=
    KazhdanCompressionCore.map_subgroup_normal K f hf
  have hTimage : HasKazhdanPropertyT.{0, 0} (K.map f) :=
    KazhdanCompressionCore.map_subgroup_hasKazhdanPropertyT K f hT
  have hfk : f k ∈ K.map f := ⟨k, hk, rfl⟩
  have hnontrivial : Nontrivial (K.map f) :=
    ⟨⟨⟨f k, hfk⟩, 1, fun h ↦ hsurvive (congrArg Subtype.val h)⟩⟩
  exact ⟨hnormal, hTimage, hnontrivial⟩

/-- Row 171: in a Hilbert-space representation, the image of the maximal
Kazhdan projection is exactly the fixed-vector projection.  This is the
faithful-representation assertion with the faithful representation already
realized concretely in `B(E)`. -/
theorem manuscriptSentence171_maximalProjectionImageIsFixedProjection
    {K : Type u} [Group K] (D : KazhdanData K)
    {E : Type (u + 1)} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (rho : K →* unitary (E →L[ℂ] E)) :
    ∃ f : MaximalGroupCStar K →⋆ₐ[ℂ] (E →L[ℂ] E),
      (∀ k : K, f (maximalGroupCStarGenerator K k) = (rho k : E →L[ℂ] E)) ∧
      ∀ x : E, f D.projection x = x ↔
        ∀ k : K, ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
  obtain ⟨f, hf, _hunique⟩ := maximalGroupCStar_existsUnique_lift_allUniverses K rho
  refine ⟨f, hf, ?_⟩
  have hgap : ∀ mu ∈ spectrum ℝ (unitaryAverage rho D.S),
      mu ≤ D.rate ∨ mu = 1 := by
    intro mu hmu
    by_cases hmu1 : mu = 1
    · exact Or.inr hmu1
    · left
      have hmuC : (mu : ℂ) ∈ spectrum ℂ (unitaryAverage rho D.S) := by
        have h := spectrum.algebraMap_mem ℂ hmu
        rwa [show (algebraMap ℝ ℂ) mu = (mu : ℂ) by simp] at h
      exact unitaryAverage_spectrum_le_manuscript rho D.kazhdan D.S
        Finset.Subset.rfl D.one_mem D.symm hmuC hmu1
  have himage : f D.projection =
      CStarSpectralProjection.spectralProjection (unitaryAverage rho D.S) D.rate :=
    image_eq_spectralProjection D rho f hf hgap
  intro x
  rw [himage, spectralProjection_apply_eq_self_iff rho
    ⟨1, D.one_mem⟩ D.symm D.rate_lt_one hgap x]
  constructor
  · intro h k
    apply apply_eq_self_of_mem_closure rho (fun s hs ↦ h s hs)
    rw [D.generates]
    trivial
  · intro h s _hs
    exact h s

/-- Row 173: normality identifies the translated fixed space with the original
fixed space, in both directions. -/
theorem manuscriptSentence173_conjugateProjectionRangeArgument
    {G : Type u} [Group G] {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (rho : G →* unitary (E →L[ℂ] E)) (K : Subgroup G) [K.Normal]
    (g : G) (x : E) :
    (∀ k ∈ K, ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        (((rho g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x) =
          ((rho g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x) ↔
      ∀ k ∈ K, ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
  exact forall_apply_eq_self_translate_iff rho
    (fun h k hk ↦ (inferInstance : K.Normal).conj_mem k hk h) g x

/-- Row 177: the Kazhdan projection compresses to zero in its complementary
corner. -/
theorem manuscriptSentence177_cornerKazhdanProjectionZero
    {A : Type*} [Ring A] {p : A} (hp : IsIdempotentElem p) :
    (1 - p) * p * (1 - p) = 0 :=
  corner_compression_kazhdanProjection hp

/-- Rows 178--179: the positive Kazhdan average dominates the printed scalar
on every vector of the complementary sector.  This is the exact quadratic-form
meaning of `b ≥ (κ²/|S|)q`. -/
theorem manuscriptSentence178_179_positiveAverageLowerBound
    {K : Type u} [Group K] {S : Finset K} {kappa : ℝ}
    (hS : IsKazhdanPair.{u, u} K S kappa)
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (rho : K →* (E ≃ₗᵢ[ℂ] E)) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    ∀ x : (KazhdanOrthogonal.invariantSubmodule (realifyHom rho))ᗮ,
      kappa ^ 2 / S.card * ‖x‖ ^ 2 ≤
        (S.card : ℝ)⁻¹ * ∑ s ∈ S,
          ‖KazhdanOrthogonal.orthogonalRepresentation (realifyHom rho) s x - x‖ ^ 2 := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  intro x
  exact corner_kazhdan_average_sq_ge hS (realifyHom rho) x

/-- Row 180, coordinate identity: the printed `b_n` is exactly the Gram sum
of the corrected corner maps. -/
theorem manuscriptSentence180_coordinateElementFormula
    {Y ι : Type*} [Fintype Y] [DecidableEq Y]
    (S : Finset ι) (W : ι → Matrix Y Y ℂ) :
    sectorGram S W = ∑ s ∈ S, (W s - 1)ᴴ * (W s - 1) :=
  rfl

/-- Rows 180--181: a corona norm lower bound for the represented coordinate
elements gives the normalized-corner trace inequality, with the exact
`o(1)` represented by an arbitrary positive epsilon. -/
theorem manuscriptSentence180_181_negativePartToCornerTrace
    (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (l : Filter ℕ) [Filter.NeBot l] {ι : Type*} (S : Finset ι)
    (W : ∀ n, ι → Matrix (Y n) (Y n) ℂ)
    (a : BoundedMatrixSequence (fun n ↦ Y n)) (t c : ℝ)
    (hrep : ∀ n, a n =
      (t : ℂ) • (1 : Matrix (Y n) (Y n) ℂ) - sectorGram S (W n))
    (hnorm : ‖Ideal.Quotient.mk
      (nullMatrixSequenceIdeal (fun n ↦ Y n) l) a‖ ≤ t - c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in l, (c - epsilon) / S.card ≤
      (S.card : ℝ)⁻¹ * ∑ s ∈ S, hsNormSq (Y n) (W n s - 1) :=
  eventually_printed_corner_trace_inequality Y l S W a t c hrep hnorm hepsilon

/-- Row 182: a uniform positive averaged corner-trace bound supplies one fixed
group element and a literal subsequence on which its Hilbert--Schmidt mass
stays positive. -/
theorem manuscriptSentence182_fixedElementSubsequence
    {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ℕ → ι → ℝ) (c : ℝ)
    (h : ∀ n, c ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, f n s) :
    ∃ s0 ∈ S, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ n, c ≤ f (phi n) s0 :=
  exists_persistent_subsequence S hS f c h

end OneSidedMFRadical
end Manuscript
end GroupApproximation
