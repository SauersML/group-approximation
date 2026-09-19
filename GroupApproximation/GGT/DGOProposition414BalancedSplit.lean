import GroupApproximation.GGT.DGOProposition414Extremal

/-!
# The raw balanced split of an extremal Proposition 4.14 input

This packages the unconditional output of the balanced-cut theorem and the
interior half-polygon construction for an arbitrary `SumBoundInput`.  It is
the source object consumed by the two component-surgery halves: the selected
corners, the common geodesic chord, both closed half words and their actual
cuts, admissible letters, and the exact side-count estimates all live in one
dependent structure.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The complete raw balanced split attached to one admissible polygon. -/
structure BalancedSplitData (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} (P : SumBoundInput D (b : ℝ) n) (k R : ℕ) where
  firstSide : ℕ
  secondSide : ℕ
  firstVertex : ℕ
  secondVertex : ℕ
  side_order : firstSide < secondSide
  secondSide_lt : secondSide < n
  quarter_lower : n ≤ 4 * (secondSide - firstSide)
  quarter_upper : 4 * (secondSide - firstSide) ≤ 3 * n
  firstVertex_mem : P.cut firstSide ≤ firstVertex ∧
    firstVertex ≤ P.cut (firstSide + 1)
  secondVertex_mem : P.cut secondSide ≤ secondVertex ∧
    secondVertex ≤ P.cut (secondSide + 1)
  chord : List (RelLetter G Λ)
  firstCut : ℕ → ℕ
  secondCut : ℕ → ℕ
  chord_geodesic : IsGeodesicWord D
    (vertex P.basepoint P.word firstVertex)
    (vertex P.basepoint P.word secondVertex) chord
  first_polygonCut : IsPolygonCut
    ((secondSide - firstSide + 1) + chord.length)
    (firstHalf P.word
      (splitPairCut P.cut firstSide secondSide firstVertex secondVertex)
      (firstSide + 1) (secondSide + 2) chord) firstCut
  second_polygonCut : IsPolygonCut
    ((n - secondSide) + firstSide + 1 + chord.length)
    (secondHalf P.word
      (splitPairCut P.cut firstSide secondSide firstVertex secondVertex)
      (firstSide + 1) (secondSide + 2) chord) secondCut
  first_closed : RelLetter.listVal
    (firstHalf P.word
      (splitPairCut P.cut firstSide secondSide firstVertex secondVertex)
      (firstSide + 1) (secondSide + 2) chord) = 1
  second_closed : RelLetter.listVal
    (secondHalf P.word
      (splitPairCut P.cut firstSide secondSide firstVertex secondVertex)
      (firstSide + 1) (secondSide + 2) chord) = 1
  first_letters : ∀ x ∈
    firstHalf P.word
      (splitPairCut P.cut firstSide secondSide firstVertex secondVertex)
      (firstSide + 1) (secondSide + 2) chord,
    D.IsLetter x
  second_letters : ∀ x ∈
    secondHalf P.word
      (splitPairCut P.cut firstSide secondSide firstVertex secondVertex)
      (firstSide + 1) (secondSide + 2) chord,
    D.IsLetter x
  chord_length_le : chord.length ≤ 6 * (δ + 6) * (k + 1) + R
  side_counts :
    (((secondSide - firstSide + 1) + chord.length) +
        ((n - secondSide) + firstSide + 1 + chord.length) =
      n + 2 + 2 * chord.length) ∧
    4 * ((secondSide - firstSide + 1) + chord.length) ≤
      3 * n + 4 + 4 * chord.length ∧
    4 * ((n - secondSide) + firstSide + 1 + chord.length) ≤
      3 * n + 4 + 4 * chord.length

/-- Every sufficiently large input has a packaged balanced split, with one
uniform additive chord constant depending only on `D`, `δ`, and `b`. -/
theorem exists_balancedSplitData (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ R : ℕ, ∀ {n k : ℕ}, 8 ≤ n → n ≤ 2 ^ k →
      ∀ P : SumBoundInput D (b : ℝ) n,
        Nonempty (BalancedSplitData D hsymm b hδ P k R) := by
  obtain ⟨R, hR⟩ := exists_balanced_interior_cut_word D (b := b + 1) hδ
  refine ⟨R, ?_⟩
  intro n k hn hk P
  let polygon : IsCutPolygon D ((b + 1 : ℕ) : ℝ) n
      P.basepoint P.word P.cut :=
    isCutPolygon_of_sumBound_shape D b n P.basepoint P.word P.cut
      P.target P.letters P.closed P.polygonCut P.target_edge P.quasi
  obtain ⟨a, c, i, j, hac, hcn, hlower, hupper, hai, hia, hcj, hjc,
    hdist⟩ := hR hn hk P.basepoint P.word P.cut polygon
  obtain ⟨chord, cut₁, cut₂, hchord, hcut₁, hcut₂, hclosed₁,
    hclosed₂, hletters₁, hletters₂, hlength, hcounts⟩ :=
    exists_interior_half_polygon_data D P.basepoint P.word P.cut
      polygon hac hcn hlower hupper hai hia hcj hjc hdist
  exact ⟨{
    firstSide := a
    secondSide := c
    firstVertex := i
    secondVertex := j
    side_order := hac
    secondSide_lt := hcn
    quarter_lower := hlower
    quarter_upper := hupper
    firstVertex_mem := ⟨hai, hia⟩
    secondVertex_mem := ⟨hcj, hjc⟩
    chord := chord
    firstCut := cut₁
    secondCut := cut₂
    chord_geodesic := hchord
    first_polygonCut := hcut₁
    second_polygonCut := hcut₂
    first_closed := hclosed₁
    second_closed := hclosed₂
    first_letters := hletters₁
    second_letters := hletters₂
    chord_length_le := hlength
    side_counts := hcounts
  }⟩

end DGOProposition414
end GGT
end GroupApproximation
