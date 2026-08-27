import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerKazhdanQuadraticBridge
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceNormalKazhdanClosure
import GroupApproximation.Analysis.PrintedDiagonalSubsequence

/-!
# Final sentence audit for the printed normal-Kazhdan corner route

This file records the sentence-level consequences of the corrected-corner
projection-zero interface.  `CorrectedCornerProjectionZeroAssembly` supplies
that interface unconditionally for the constructed provenance-rich corner,
and `NormalKazhdanUnconditionalClosure` composes it with these consequences.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix PrintedCornerCompression
open AbstractSpectralGap PrintedDiagonalSubsequence
open MaximalCStarKazhdanProjection UnitaryAverageFixedVector
open UltraproductKazhdanProjection
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u v

variable {G : Type} [Group G]
variable {model : ℕ → FiniteModel}

/-- Sentence 171 without an artificial universe restriction on the faithful
Hilbert-space representation.  The Kazhdan pair stored for `Cmax(K)` first
descends to the group universe and then lifts to the arbitrary universe of
`E`. -/
theorem manuscriptSentence171_maximalProjectionImageIsFixedProjection_allUniverses
    {K : Type u} [Group K] (D : KazhdanData K)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (rho : K →* unitary (E →L[ℂ] E)) :
    ∃ f : MaximalGroupCStar K →⋆ₐ[ℂ] (E →L[ℂ] E),
      (∀ k : K,
        f (maximalGroupCStarGenerator K k) = (rho k : E →L[ℂ] E)) ∧
      ∀ x : E, f D.projection x = x ↔
        ∀ k : K,
          ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
  obtain ⟨f, hf, _hunique⟩ :=
    maximalGroupCStar_existsUnique_lift_allUniverses K rho
  refine ⟨f, hf, ?_⟩
  have hKsmall : IsKazhdanPair.{u, u} K D.S D.kappa :=
    IsKazhdanPair.lowerUniverse.{u, u + 1} D.kazhdan
  have hKatE : IsKazhdanPair.{u, v} K D.S D.kappa :=
    IsKazhdanPair.liftUniverse.{u, v} hKsmall
  have hgap : ∀ mu ∈ spectrum ℝ (unitaryAverage rho D.S),
      mu ≤ D.rate ∨ mu = 1 := by
    intro mu hmu
    by_cases hmu1 : mu = 1
    · exact Or.inr hmu1
    · left
      have hmuC : (mu : ℂ) ∈ spectrum ℂ (unitaryAverage rho D.S) := by
        have h := spectrum.algebraMap_mem ℂ hmu
        rwa [show (algebraMap ℝ ℂ) mu = (mu : ℂ) by simp] at h
      exact unitaryAverage_spectrum_le_manuscript rho
        hKatE D.S Finset.Subset.rfl
          D.one_mem D.symm hmuC hmu1
  have himage : f D.projection =
      CStarSpectralProjection.spectralProjection
        (unitaryAverage rho D.S) D.rate :=
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

/-- Sentence 173 for a representation space in an arbitrary universe. -/
theorem manuscriptSentence173_conjugateProjectionRangeArgument_allUniverses
    {H : Type u} [Group H] {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (rho : H →* unitary (E →L[ℂ] E)) (K : Subgroup H) [K.Normal]
    (g : H) (x : E) :
    (∀ k ∈ K, ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        (((rho g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x) =
          ((rho g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x) ↔
      ∀ k ∈ K,
        ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
  exact forall_apply_eq_self_translate_iff rho
    (fun h k hk ↦ (inferInstance : K.Normal).conj_mem k hk h) g x

/-- An eventual averaged lower bound along a free ultrafilter gives the
literal fixed-element subsequence asserted in sentence 182.  This is the
filter-level form missing from `manuscriptSentence182_fixedElementSubsequence`,
whose premise is pointwise in every coordinate. -/
theorem exists_fixedElementSubsequence_of_eventually_average
    {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (f : ℕ → ι → ℝ) (c : ℝ)
    (h : ∀ᶠ n in (ω : Filter ℕ),
      c ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, f n s) :
    ∃ s0 ∈ S, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ n, c ≤ f (phi n) s0 := by
  let A : Set ℕ :=
    {n | c ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, f n s}
  have hA : A ∈ (ω : Filter ℕ) := h
  obtain ⟨psi, hpsi, hpsiA, _⟩ :=
    exists_strictMono_mem_tendsto_atTop (X := ℝ) hω hA
      (fun _ _ ↦ (0 : ℝ)) (fun _ ↦ 0) (fun _ ↦ tendsto_const_nhds)
  have hall : ∀ n,
      c ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, f (psi n) s :=
    fun n ↦ hpsiA n
  obtain ⟨s0, hs0, phi, hphi, hbound⟩ :=
    manuscriptSentence182_fixedElementSubsequence S hS
      (fun n s ↦ f (psi n) s) c hall
  exact ⟨s0, hs0, psi ∘ phi, hpsi.comp hphi, hbound⟩

/-- Sentences 178--181 on the actual polar-corrected maps.  The former
quadratic-form and coordinate-representative premises have both been
constructed internally.  `CorrectedCornerProjectionZeroAssembly` supplies the
named complementary-projection identification unconditionally, and
`NormalKazhdanUnconditionalClosure` composes it with this theorem. -/
theorem manuscriptSentences178_181_correctedCornerTrace
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
  eventually_correctedCorner_trace_inequality_of_projectionZero
    D ω hω K hzero hepsilon

/-- **Sentence 182 for the actual corrected corners.**  One fixed Kazhdan-set
element stays a uniformly positive normalized Hilbert--Schmidt distance from
the corner identity on a literal subsequence. -/
theorem manuscriptSentence182_correctedCornerFixedElementSubsequence
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (K : KazhdanData G)
    (hzero : CorrectedCornerKazhdanProjectionZero D ω hω K) :
    ∃ s0 ∈ K.S, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ n,
        K.kappa ^ 2 / (2 * K.S.card) ≤
          hsNormSq (D.cornerModel (phi n))
            ((D.cornerMap (phi n) s0 :
              Matrix (D.cornerModel (phi n))
                (D.cornerModel (phi n)) ℂ) - 1) := by
  have hkappa : 0 < K.kappa := K.kazhdan.1
  have hkappaSqHalf : 0 < K.kappa ^ 2 / 2 := by
    positivity
  have hScard : (K.S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, K.one_mem⟩)
  have hevent := manuscriptSentences178_181_correctedCornerTrace
    D ω hω K hzero hkappaSqHalf
  have hevent' : ∀ᶠ n in (ω : Filter ℕ),
      K.kappa ^ 2 / (2 * K.S.card) ≤
        (K.S.card : ℝ)⁻¹ * ∑ s ∈ K.S,
          hsNormSq (D.cornerModel n)
            ((D.cornerMap n s :
              Matrix (D.cornerModel n) (D.cornerModel n) ℂ) - 1) := by
    filter_upwards [hevent] with n hn
    calc
      K.kappa ^ 2 / (2 * K.S.card) =
          (K.kappa ^ 2 - K.kappa ^ 2 / 2) / K.S.card := by
            (field_simp [hScard]; ring)
      _ ≤ (K.S.card : ℝ)⁻¹ * ∑ s ∈ K.S,
          hsNormSq (D.cornerModel n)
            ((D.cornerMap n s :
              Matrix (D.cornerModel n) (D.cornerModel n) ℂ) - 1) := hn
  exact exists_fixedElementSubsequence_of_eventually_average
    K.S ⟨1, K.one_mem⟩ ω hω
    (fun n s ↦ hsNormSq (D.cornerModel n)
      ((D.cornerMap n s :
        Matrix (D.cornerModel n) (D.cornerModel n) ℂ) - 1))
    (K.kappa ^ 2 / (2 * K.S.card)) hevent'

/-- **Sentence 156 on the actual finite-dimensional corner sector.**  The
Kazhdan inequality detects the corrected corona image by a fixed element of
the Kazhdan set whose normalized Hilbert--Schmidt displacement has a strictly
positive lower bound along a subsequence.  The complementary-projection input
is supplied unconditionally by `CorrectedCornerProjectionZeroAssembly` and
composed with this detection theorem in `NormalKazhdanUnconditionalClosure`. -/
theorem manuscriptSentence156_correctedCornerKazhdanDetection
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (K : KazhdanData G)
    (hzero : CorrectedCornerKazhdanProjectionZero D ω hω K) :
    ∃ s0 ∈ K.S, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ n,
        0 < K.kappa ^ 2 / (2 * K.S.card) ∧
          K.kappa ^ 2 / (2 * K.S.card) ≤
            hsNormSq (D.cornerModel (phi n))
              ((D.cornerMap (phi n) s0 :
                Matrix (D.cornerModel (phi n))
                  (D.cornerModel (phi n)) ℂ) - 1) := by
  obtain ⟨s0, hs0, phi, hphi, hbound⟩ :=
    manuscriptSentence182_correctedCornerFixedElementSubsequence
      D ω hω K hzero
  refine ⟨s0, hs0, phi, hphi, fun n ↦ ⟨?_, hbound n⟩⟩
  have hkappa : 0 < K.kappa := K.kazhdan.1
  have hcard : 0 < (K.S.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨1, K.one_mem⟩)
  positivity

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
