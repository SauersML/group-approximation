import GroupApproximation.GGT.DGOProposition414GapLeftConnectorWrapped

/-!
# The chord block of a balanced half word

Each half word of the balanced split is its inherited arc followed by the
cutting chord: the first half reads the chord backwards, the wrapped half
forwards.  This file records the resulting dictionary between forward chord
coordinates and half-word positions, together with the head letter of an
oriented child chord.  It is the bridge the remaining Proposition 4.14 seams
need, because the isolation certificate of a surviving source lives in the
half word while the seam letters are named on the chord.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The head letter of an oriented child chord -/

/-- A forward child segment starting at `y + 1` opens with `word[y+1]`. -/
theorem isCompOf_head_orientedSegment_succ_iff
    (lam : Λ) (word : List (RelLetter G Λ)) {y cf : ℕ}
    (hle : y + 1 ≤ cf) (hy : y + 1 < word.length)
    (hseg : 0 < (orientedSegment word (y + 1) cf).length) :
    ((orientedSegment word (y + 1) cf)[0]'hseg).IsCompOf lam ↔
      (word[y + 1]'hy).IsCompOf lam := by
  have heq : orientedSegment word (y + 1) cf =
      (word.drop (y + 1)).take (cf - (y + 1)) := by
    rw [orientedSegment, if_pos hle]
  rw [List.getElem_of_eq heq hseg]
  simp

/-- A backward child segment starting at `y` opens with the inverse of
`word[y-1]`, which carries the same labels. -/
theorem isCompOf_head_orientedSegment_pred_iff
    (lam : Λ) (word : List (RelLetter G Λ)) {y cf : ℕ}
    (hle : cf ≤ y) (hy : y ≤ word.length)
    (hy1 : y - 1 < word.length)
    (hseg : 0 < (orientedSegment word y cf).length) :
    ((orientedSegment word y cf)[0]'hseg).IsCompOf lam ↔
      (word[y - 1]'hy1).IsCompOf lam := by
  have hcfy : cf < y := by
    by_contra hcon
    have hyc : y ≤ cf := by omega
    have hzero : (orientedSegment word y cf).length = 0 := by
      rw [orientedSegment, if_pos hyc, show y = cf from le_antisymm hyc hle]
      simp
    omega
  have hne : ¬ (y ≤ cf) := by omega
  have heq : orientedSegment word y cf =
      revWord ((word.drop cf).take (y - cf)) := by
    rw [orientedSegment, if_neg hne]
  have hLlen : ((word.drop cf).take (y - cf)).length = y - cf := by
    rw [List.length_take, List.length_drop]
    omega
  have hrev : 0 < (revWord ((word.drop cf).take (y - cf))).length := by
    rw [OsinComponents.length_revWord, hLlen]
    omega
  have ht : ((word.drop cf).take (y - cf)).length - 1 <
      ((word.drop cf).take (y - cf)).length := by
    rw [hLlen]
    omega
  have hiff := isCompOf_getElem_revWord' ((word.drop cf).take (y - cf)) lam
    (m := 0) hrev ht rfl
  have hidx : cf + (((word.drop cf).take (y - cf)).length - 1) = y - 1 := by
    rw [hLlen]
    omega
  rw [List.getElem_of_eq heq hseg, hiff, List.getElem_take, List.getElem_drop,
    getElem_congr_idx (c := word) hidx]

namespace BalancedSplitData

/-! ## The first half reads the chord backwards -/

/-- The first half word is its inherited arc followed by the reversed
chord. -/
theorem firstWord_eq_append
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstWord = B.firstArc ++ revWord B.chord := rfl

/-- The inherited first arc has the recorded length. -/
theorem firstArc_length_eq
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstArc.length = B.firstArcLength := by
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [show B.refinedCut (B.secondSide + 2) = B.secondVertex by
      simp [refinedCut, splitPairCut_right]]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  show (arcWord P.word B.refinedCut (B.firstSide + 1)
    (B.secondSide + 2)).length = B.firstArcLength
  rw [length_arcWord P.word B.refinedCut hEnd]
  simp [firstArcLength, refinedCut, splitPairCut_left B.side_order,
    splitPairCut_right]

/-- The first half word has arc length plus chord length. -/
theorem firstWord_length_eq
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstWord.length = B.firstArcLength + B.chord.length := by
  rw [B.firstWord_eq_append, List.length_append,
    OsinComponents.length_revWord, B.firstArc_length_eq]

/-- Forward chord coordinates land inside the first half word. -/
theorem firstChordPos_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (y : ℕ) (hy : y < B.chord.length) :
    B.firstChordPos y < B.firstWord.length := by
  rw [B.firstWord_length_eq]
  simp only [firstChordPos]
  omega

/-- Successive forward chord coordinates are adjacent, in the opposite order,
in the first half word. -/
theorem firstChordPos_succ
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (y : ℕ) (hy : y + 1 < B.chord.length) :
    B.firstChordPos (y + 1) + 1 = B.firstChordPos y := by
  simp only [firstChordPos]
  omega

/-- The predecessor forward chord coordinate sits one later in the first half
word. -/
theorem firstChordPos_pred
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (y : ℕ) (hpos : 0 < y) (hy : y < B.chord.length) :
    B.firstChordPos (y - 1) = B.firstChordPos y + 1 := by
  simp only [firstChordPos]
  omega

/-- A chord letter keeps its labels at its first-half position. -/
theorem isCompOf_firstWord_chordPos_iff
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (lam : Λ) (y : ℕ) (hy : y < B.chord.length)
    (hpos : B.firstChordPos y < B.firstWord.length) :
    (B.firstWord[B.firstChordPos y]'hpos).IsCompOf lam ↔
      (B.chord[y]'hy).IsCompOf lam := by
  have harc := B.firstArc_length_eq
  have hidx : B.firstChordPos y =
      B.firstArc.length + (B.chord.length - 1 - y) := by
    rw [harc]
    simp only [firstChordPos]
  have hrevLt : B.chord.length - 1 - y < (revWord B.chord).length := by
    rw [OsinComponents.length_revWord]
    omega
  have hstep : B.firstWord[B.firstChordPos y]'hpos =
      (revWord B.chord)[B.chord.length - 1 - y]'hrevLt := by
    rw [List.getElem_of_eq B.firstWord_eq_append hpos,
      getElem_congr_idx (c := B.firstArc ++ revWord B.chord) hidx,
      List.getElem_append_right (by omega)]
    exact getElem_congr_idx (by omega)
  rw [hstep]
  exact isCompOf_getElem_revWord' B.chord lam hrevLt hy (by omega)

/-! ## The wrapped half reads the chord forwards -/

/-- The wrapped half word is its inherited arc followed by the chord. -/
theorem secondWord_eq_append
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondWord = B.secondArc ++ B.chord := by
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  unfold secondWord secondArc
  simp only [secondHalf]
  rw [hleft, hright]

/-- The inherited wrapped arc has the recorded length. -/
theorem secondArc_length_eq
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondArc.length = B.secondArcLength := by
  have hsecondLe : B.secondVertex ≤ P.word.length :=
    B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hfirstLe : B.firstVertex ≤ P.word.length :=
    B.split_vertices_ordered.trans hsecondLe
  show (P.word.drop B.secondVertex ++ P.word.take B.firstVertex).length =
    B.secondArcLength
  rw [List.length_append, List.length_drop, List.length_take]
  simp only [secondArcLength]
  omega

/-- The wrapped half word has arc length plus chord length. -/
theorem secondWord_length_eq
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondWord.length = B.secondArcLength + B.chord.length := by
  rw [B.secondWord_eq_append, List.length_append, B.secondArc_length_eq]

/-- Forward chord coordinates land inside the wrapped half word. -/
theorem secondChordPos_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (y : ℕ) (hy : y < B.chord.length) :
    B.secondChordPos y < B.secondWord.length := by
  rw [B.secondWord_length_eq]
  simp only [secondChordPos]
  omega

/-- Successive forward chord coordinates are adjacent, in the same order, in
the wrapped half word. -/
theorem secondChordPos_succ
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (y : ℕ) :
    B.secondChordPos (y + 1) = B.secondChordPos y + 1 := by
  simp only [secondChordPos]
  omega

/-- A chord letter keeps its labels at its wrapped position. -/
theorem isCompOf_secondWord_chordPos_iff
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (lam : Λ) (y : ℕ) (hy : y < B.chord.length)
    (hpos : B.secondChordPos y < B.secondWord.length) :
    (B.secondWord[B.secondChordPos y]'hpos).IsCompOf lam ↔
      (B.chord[y]'hy).IsCompOf lam := by
  have harc := B.secondArc_length_eq
  have hidx : B.secondChordPos y = B.secondArc.length + y := by
    rw [harc]
    simp only [secondChordPos]
  have hstep : B.secondWord[B.secondChordPos y]'hpos =
      B.chord[y]'hy := by
    rw [List.getElem_of_eq B.secondWord_eq_append hpos,
      getElem_congr_idx (c := B.secondArc ++ B.chord) hidx,
      List.getElem_append_right (by omega)]
    exact getElem_congr_idx (by omega)
  rw [hstep]

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
