import GroupApproximation.GGT.HullSCLemma44ReducedDiagram
import GroupApproximation.GGT.HullSCFillingNonElementary
import GroupApproximation.GGT.HullLemmaEe

/-!
# The exterior-arc contradiction in Hull's Lemma 4.4

Once a reduced relative diagram supplies a cell whose interior boundary has at
most three contiguity arcs, the rest of the injectivity argument is numerical.
Each interior arc is a published `eps`-piece and hence has length less than
`mu` times the cell relator.  At `mu ≤ 1/16` the exterior prefix has more than
`13/16` of the relator.  Its `(4,1)` quasi-geodesicity makes its value too long
to be joined to the short diagram boundary by two `eps`-connectors.

This file proves that complete implication.  The remaining geometric step is
only the production of the explicit three-arc cell below from a reduced
diagram; no small-cancellation arithmetic remains hidden in that step.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-- The explicit output of the planar contiguity step: one oriented relator
cell, an exterior prefix, and at most three interior published pieces.  The
three source words are rotations of the cell boundary at the level needed by
the estimate: they belong to the family and have the same length. -/
structure Lemma44ThreePieceExteriorCell {G : Type u} [Group G]
    {Λ : Type w} (E : GGT.RelGenSet G Λ)
    (W : Set (List (GGT.RelLetter G Λ))) (eps : ℕ) (boundary : G) where
  relator : List (GGT.RelLetter G Λ)
  relator_mem : relator ∈ W
  exterior : List (GGT.RelLetter G Λ)
  piece₁ : List (GGT.RelLetter G Λ)
  piece₂ : List (GGT.RelLetter G Λ)
  piece₃ : List (GGT.RelLetter G Λ)
  relator_decomposition :
    relator = exterior ++ piece₁ ++ piece₂ ++ piece₃
  comparison₁ : List (GGT.RelLetter G Λ)
  comparison₂ : List (GGT.RelLetter G Λ)
  comparison₃ : List (GGT.RelLetter G Λ)
  source₁ : List (GGT.RelLetter G Λ)
  source₂ : List (GGT.RelLetter G Λ)
  source₃ : List (GGT.RelLetter G Λ)
  contiguity₁ : RelWord.IsPublishedPiece E W eps piece₁ comparison₁ source₁
  contiguity₂ : RelWord.IsPublishedPiece E W eps piece₂ comparison₂ source₂
  contiguity₃ : RelWord.IsPublishedPiece E W eps piece₃ comparison₃ source₃
  source₁_length : source₁.length = relator.length
  source₂_length : source₂.length = relator.length
  source₃_length : source₃.length = relator.length
  leftConnector : G
  rightConnector : G
  leftConnector_short : wordNorm E.base leftConnector ≤ eps
  rightConnector_short : wordNorm E.base rightConnector ≤ eps
  exterior_value : GGT.RelLetter.listVal exterior =
    leftConnector * boundary * rightConnector

/-- **The quantitative exterior-arc contradiction.**

The threshold is stated in the exact real-valued form consumed by the proof:
`13 rho / 16` exceeds four times the maximum relative length of an exterior
arc joined to a radius-`R` boundary by two `eps`-connectors. -/
theorem false_of_lemma44ThreePieceExteriorCell
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (P : AuxiliaryPeripheralFamily A N S)
    {W : Set (List
      (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {R eps rho : ℕ} {mu : ℝ}
    (Z : Lemma44ReducedRelatorDiagram A.alphabet W R)
    (hsc : RelWord.IsLemma44Input P.rel W eps mu rho)
    (hmu : mu ≤ 1 / 16)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (13 / 16 : ℝ) * (rho : ℝ))
    (C : Lemma44ThreePieceExteriorCell P.rel W eps Z.boundary) : False := by
  have hp₁raw := hsc.publishedPiecesSmall C.piece₁ C.comparison₁ C.source₁
    C.contiguity₁
  have hp₂raw := hsc.publishedPiecesSmall C.piece₂ C.comparison₂ C.source₂
    C.contiguity₂
  have hp₃raw := hsc.publishedPiecesSmall C.piece₃ C.comparison₃ C.source₃
    C.contiguity₃
  have hp₁ : (C.piece₁.length : ℝ) < mu * C.relator.length := by
    have h := lt_of_le_of_lt (le_max_left _ _) hp₁raw
    rwa [C.source₁_length] at h
  have hp₂ : (C.piece₂.length : ℝ) < mu * C.relator.length := by
    have h := lt_of_le_of_lt (le_max_left _ _) hp₂raw
    rwa [C.source₂_length] at h
  have hp₃ : (C.piece₃.length : ℝ) < mu * C.relator.length := by
    have h := lt_of_le_of_lt (le_max_left _ _) hp₃raw
    rwa [C.source₃_length] at h
  have hlenNat : C.relator.length = C.exterior.length + C.piece₁.length +
      C.piece₂.length + C.piece₃.length := by
    rw [C.relator_decomposition]
    simp only [List.length_append]
  have hlen : (C.relator.length : ℝ) = (C.exterior.length : ℝ) +
      C.piece₁.length + C.piece₂.length + C.piece₃.length := by
    exact_mod_cast hlenNat
  have hexterior_fraction :
      (13 / 16 : ℝ) * C.relator.length < C.exterior.length := by
    have hcoeff : (13 / 16 : ℝ) ≤ 1 - 3 * mu := by linarith
    have hnonneg : (0 : ℝ) ≤ C.relator.length := Nat.cast_nonneg _
    have hcoeffMul : (13 / 16 : ℝ) * C.relator.length ≤
        (1 - 3 * mu) * C.relator.length :=
      mul_le_mul_of_nonneg_right hcoeff hnonneg
    linarith
  have hlongNat : rho ≤ C.relator.length := hsc.long C.relator C.relator_mem
  have hlong : (rho : ℝ) ≤ C.relator.length := by exact_mod_cast hlongNat
  have hexterior_long :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) < C.exterior.length := by
    have hscale : (13 / 16 : ℝ) * (rho : ℝ) ≤
        (13 / 16 : ℝ) * C.relator.length :=
      mul_le_mul_of_nonneg_left hlong (by norm_num)
    exact lt_trans hthreshold (lt_of_le_of_lt hscale hexterior_fraction)
  have hexterior_le : C.exterior.length ≤ C.relator.length := by
    rw [C.relator_decomposition]
    simp only [List.length_append]
    omega
  have htake : C.relator.take C.exterior.length = C.exterior := by
    rw [C.relator_decomposition]
    simp
  have hqg := hsc.quasiGeodesic C.relator C.relator_mem
  have hlowerRaw := (hqg 0 C.exterior.length (Nat.zero_le _)
    hexterior_le).1
  have hzero : GGT.RelLetter.listVal (C.relator.take 0) = 1 := by
    simp [GGT.RelLetter.listVal]
  dsimp only at hlowerRaw
  rw [hzero, htake, wordDist_one_left] at hlowerRaw
  have hlower : (C.exterior.length : ℝ) / 4 - 1 ≤
      (wordNorm P.rel.alphabet.carrier
        (GGT.RelLetter.listVal C.exterior) : ℝ) := by
    norm_num at hlowerRaw ⊢
    exact hlowerRaw
  have hbaseSubset : A.alphabet.carrier ⊆ P.rel.alphabet.carrier := by
    intro a ha
    apply GGT.base_subset_alphabet_carrier P.rel
    rw [P.base_eq]
    exact ha
  have hleftRel : wordNorm P.rel.alphabet.carrier C.leftConnector ≤ eps :=
    le_trans (wordNorm_mono hbaseSubset
      (wordLengths_nonempty A.alphabet.symmetricGenerating C.leftConnector))
      (by rw [← P.base_eq]; exact C.leftConnector_short)
  have hrightRel : wordNorm P.rel.alphabet.carrier C.rightConnector ≤ eps :=
    le_trans (wordNorm_mono hbaseSubset
      (wordLengths_nonempty A.alphabet.symmetricGenerating C.rightConnector))
      (by rw [← P.base_eq]; exact C.rightConnector_short)
  have hboundaryRel : wordNorm P.rel.alphabet.carrier Z.boundary ≤ 2 * R :=
    le_trans (wordNorm_mono hbaseSubset
      (wordLengths_nonempty A.alphabet.symmetricGenerating Z.boundary))
      Z.boundary_length_le
  have hmul₁ := wordNorm_mul_le P.rel.alphabet.symmetricGenerating
    C.leftConnector Z.boundary
  have hmul₂ := wordNorm_mul_le P.rel.alphabet.symmetricGenerating
    (C.leftConnector * Z.boundary) C.rightConnector
  have hupper : wordNorm P.rel.alphabet.carrier
      (GGT.RelLetter.listVal C.exterior) ≤ 2 * R + 2 * eps := by
    rw [C.exterior_value]
    omega
  have hupperReal :
      (wordNorm P.rel.alphabet.carrier
        (GGT.RelLetter.listVal C.exterior) : ℝ) ≤
          ((2 * R + 2 * eps : ℕ) : ℝ) := by
    exact_mod_cast hupper
  have hlowerStrict :
      ((2 * R + 2 * eps : ℕ) : ℝ) < C.exterior.length / 4 - 1 := by
    have hfour : (0 : ℝ) < 4 := by norm_num
    have hcast : ((2 * R + 2 * eps + 1 : ℕ) : ℝ) =
        ((2 * R + 2 * eps : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast] at hexterior_long
    linarith
  linarith

end HullSC
end GroupApproximation
