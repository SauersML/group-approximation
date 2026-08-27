import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerProjectionZeroAssembly
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanSentenceAudit

/-!
# Unconditional closure of the printed normal-Kazhdan corner sentences

The complement-corner projection-zero seam is discharged by
`exists_correctedCornerKazhdanProjectionZero`.  The declarations below only
compose that assembly with the already proved sentence-level trace,
subsequence, and positive-detection theorems.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix PrintedCornerCompression
open MaximalCStarKazhdanProjection
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G] [Countable G]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- **Sentences 178--181, unconditionally from the unchanged ambient
hypotheses.**  One provenance-rich complementary corner works for every free
ultrafilter refining `cofinite` and every positive error tolerance. -/
theorem exists_normalKazhdan_unconditionalSentences178_181
    (K : Subgroup G) [K.Normal]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData K) (k : K)
    (hk : ((rho (k : G) : unitary
      (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1) :
    ∃ P : CorrectedCornerProvenanceData G X K,
      ∀ (ω : Ultrafilter ℕ) (_hω : (ω : Filter ℕ) ≤ cofinite)
        {epsilon : ℝ}, 0 < epsilon →
        ∀ᶠ n in (ω : Filter ℕ),
          (P.kazhdan.kappa ^ 2 - epsilon) / P.kazhdan.S.card ≤
            (P.kazhdan.S.card : ℝ)⁻¹ * ∑ s ∈ P.kazhdan.S,
              hsNormSq ((P.subgroupCorner K).cornerModel n)
                (((P.subgroupCorner K).cornerMap n s :
                  Matrix ((P.subgroupCorner K).cornerModel n)
                    ((P.subgroupCorner K).cornerModel n) ℂ) - 1) := by
  obtain ⟨P, hzero⟩ :=
    exists_correctedCornerKazhdanProjectionZero K rho KD k hk
  refine ⟨P, fun ω hω {_epsilon} hepsilon ↦ ?_⟩
  exact manuscriptSentences178_181_correctedCornerTrace
    (P.subgroupCorner K) ω hω P.kazhdan (hzero ω hω) hepsilon

/-- **Sentence 182, unconditionally from the unchanged ambient hypotheses.**
For the chosen complementary corner, every refining omega yields one fixed
Kazhdan-set element with a positive Hilbert--Schmidt lower bound on a literal
subsequence. -/
theorem exists_normalKazhdan_unconditionalSentence182
    (K : Subgroup G) [K.Normal]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData K) (k : K)
    (hk : ((rho (k : G) : unitary
      (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1) :
    ∃ P : CorrectedCornerProvenanceData G X K,
      ∀ (ω : Ultrafilter ℕ) (_hω : (ω : Filter ℕ) ≤ cofinite),
        ∃ s0 ∈ P.kazhdan.S, ∃ phi : ℕ → ℕ, StrictMono phi ∧
          ∀ n,
            P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) ≤
              hsNormSq ((P.subgroupCorner K).cornerModel (phi n))
                (((P.subgroupCorner K).cornerMap (phi n) s0 :
                  Matrix ((P.subgroupCorner K).cornerModel (phi n))
                    ((P.subgroupCorner K).cornerModel (phi n)) ℂ) - 1) := by
  obtain ⟨P, hzero⟩ :=
    exists_correctedCornerKazhdanProjectionZero K rho KD k hk
  refine ⟨P, fun ω hω ↦ ?_⟩
  exact manuscriptSentence182_correctedCornerFixedElementSubsequence
    (P.subgroupCorner K) ω hω P.kazhdan (hzero ω hω)

/-- **Sentence 156, unconditionally from the unchanged ambient hypotheses.**
For the chosen complementary corner, every refining omega detects the
nontrivial subgroup image by a fixed Kazhdan-set element at a strictly
positive normalized Hilbert--Schmidt distance along a subsequence. -/
theorem exists_normalKazhdan_unconditionalSentence156
    (K : Subgroup G) [K.Normal]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData K) (k : K)
    (hk : ((rho (k : G) : unitary
      (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1) :
    ∃ P : CorrectedCornerProvenanceData G X K,
      ∀ (ω : Ultrafilter ℕ) (_hω : (ω : Filter ℕ) ≤ cofinite),
        ∃ s0 ∈ P.kazhdan.S, ∃ phi : ℕ → ℕ, StrictMono phi ∧
          ∀ n,
            0 < P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) ∧
              P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) ≤
                hsNormSq ((P.subgroupCorner K).cornerModel (phi n))
                  (((P.subgroupCorner K).cornerMap (phi n) s0 :
                    Matrix ((P.subgroupCorner K).cornerModel (phi n))
                      ((P.subgroupCorner K).cornerModel (phi n)) ℂ) - 1) := by
  obtain ⟨P, hzero⟩ :=
    exists_correctedCornerKazhdanProjectionZero K rho KD k hk
  refine ⟨P, fun ω hω ↦ ?_⟩
  exact manuscriptSentence156_correctedCornerKazhdanDetection
    (P.subgroupCorner K) ω hω P.kazhdan (hzero ω hω)

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
