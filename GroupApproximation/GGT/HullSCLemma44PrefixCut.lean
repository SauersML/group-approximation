import GroupApproximation.GGT.HullSCConeOff
import GroupApproximation.GGT.HullSCLemma44PrefixGeometry
import GroupApproximation.GGT.HullSCLemma44RelativeDehn

/-!
# Prefix-length control for a Greendlinger cut

The boundary shortening in Osin's proof replaces a long exterior arc of one
relator cell by three pieces: the inverse left side, the inverse complementary
relator arc, and the inverse right side.  In the original relative alphabet
the complementary arc can be long.  In the prefix-enlarged alphabet it costs
one letter: cyclic symmetry makes the complement a prefix of a rotated
relator, and prefix values were added to the base.

This file proves the resulting sharp bound `2 * eps + 1`.  It holds first in
the source prefix alphabet and then in its quotient image.  The quotient form
says that the endpoints of every exterior boundary arc selected by a
Greendlinger certificate have prefix-quotient distance at most
`2 * eps + 1`.  This is the bounded-cell shortcut used in the hyperbolicity
part of Osin Lemma 5.1 and DGO Theorem 7.19.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

namespace RelativeBoundaryContiguity

/-! ## The complementary arc is a prefix letter -/

/-- The complementary relator arc is a prefix of the cyclic rotation that
starts at that arc. -/
theorem remainder_mem_prefixValues
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    GGT.RelLetter.listVal C.remainder ∈ RelWord.prefixValues W := by
  let rotated := relator.rotate C.exterior.length
  have hrotated : rotated ∈ W :=
    hsc.rotate_mem relator hrelator C.exterior.length
  have hsplit : rotated = C.remainder ++ C.exterior := by
    dsimp only [rotated]
    calc
      relator.rotate C.exterior.length =
          (C.exterior ++ C.remainder).rotate C.exterior.length :=
        congrArg (fun word => word.rotate C.exterior.length)
          C.relator_decomposition
      _ = C.remainder ++ C.exterior := by
        rw [List.rotate_append_length_eq]
  exact RelWord.listVal_mem_prefixValues hrotated hsplit

/-- The inverse value of the complementary arc is also a prefix value. -/
theorem inv_remainder_mem_prefixValues
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    (GGT.RelLetter.listVal C.remainder)⁻¹ ∈ RelWord.prefixValues W :=
  RelWord.inv_mem_prefixValues hsc
    (C.remainder_mem_prefixValues hsc hrelator)

/-- The inverse value of a legal old relative word has prefix-enlarged norm at
most the old word length. -/
theorem wordNorm_inv_listVal_adjoinRelatorPrefixes_le_length
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (word : List (GGT.RelLetter G Lambda))
    (hword : RelWord.IsAdmissible D word) :
    wordNorm (D.adjoinRelatorPrefixes W hsc).alphabet.carrier
      (GGT.RelLetter.listVal word)⁻¹ ≤ word.length := by
  let E := D.adjoinRelatorPrefixes W hsc
  have hold : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal word) ≤ word.length :=
    wordNorm_listVal_le_length D word hword
  have hnew : wordNorm E.alphabet.carrier
      (GGT.RelLetter.listVal word) ≤
      wordNorm D.alphabet.carrier (GGT.RelLetter.listVal word) :=
    wordNorm_mono (alphabet_subset_adjoinRelatorPrefixes D W hsc)
      (wordLengths_nonempty D.alphabet.symmetricGenerating _)
  rw [wordNorm_inv E.alphabet.symmetricGenerating]
  exact le_trans hnew hold

/-! ## The source prefix shortcut -/

/-- The complementary relator value costs at most one in the source prefix
alphabet. -/
theorem wordNorm_inv_remainder_adjoinRelatorPrefixes_le_one
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    wordNorm (D.adjoinRelatorPrefixes W hsc).alphabet.carrier
      (GGT.RelLetter.listVal C.remainder)⁻¹ ≤ 1 := by
  apply wordNorm_le_one_of_mem
  exact Set.mem_union_left _ (Set.mem_union_right _
    (C.inv_remainder_mem_prefixValues hsc hrelator))

/-- A Greendlinger replacement has source prefix norm at most
`2 * eps + 1`. -/
theorem wordNorm_replacementWord_adjoinRelatorPrefixes_le
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    wordNorm (D.adjoinRelatorPrefixes W hsc).alphabet.carrier
      C.replacementWord.prod ≤ 2 * eps + 1 := by
  let E := D.adjoinRelatorPrefixes W hsc
  have hleft : wordNorm E.alphabet.carrier
      (GGT.RelLetter.listVal C.leftSide)⁻¹ ≤ C.leftSide.length :=
    wordNorm_inv_listVal_adjoinRelatorPrefixes_le_length D W hsc
      C.leftSide C.leftSide_admissible
  have hmiddle : wordNorm E.alphabet.carrier
      (GGT.RelLetter.listVal C.remainder)⁻¹ ≤ 1 :=
    C.wordNorm_inv_remainder_adjoinRelatorPrefixes_le_one hsc hrelator
  have hright : wordNorm E.alphabet.carrier
      (GGT.RelLetter.listVal C.rightSide)⁻¹ ≤ C.rightSide.length :=
    wordNorm_inv_listVal_adjoinRelatorPrefixes_le_length D W hsc
      C.rightSide C.rightSide_admissible
  have hleftSideShort : C.leftSide.length ≤ eps := C.leftSide_short
  have hrightSideShort : C.rightSide.length ≤ eps := C.rightSide_short
  rw [C.replacementWord_prod]
  calc
    wordNorm E.alphabet.carrier
        ((GGT.RelLetter.listVal C.leftSide)⁻¹ *
          (GGT.RelLetter.listVal C.remainder)⁻¹ *
            (GGT.RelLetter.listVal C.rightSide)⁻¹) ≤
        wordNorm E.alphabet.carrier
            ((GGT.RelLetter.listVal C.leftSide)⁻¹ *
              (GGT.RelLetter.listVal C.remainder)⁻¹) +
          wordNorm E.alphabet.carrier
            (GGT.RelLetter.listVal C.rightSide)⁻¹ :=
      wordNorm_mul_le E.alphabet.symmetricGenerating _ _
    _ ≤ (wordNorm E.alphabet.carrier
            (GGT.RelLetter.listVal C.leftSide)⁻¹ +
          wordNorm E.alphabet.carrier
            (GGT.RelLetter.listVal C.remainder)⁻¹) +
        wordNorm E.alphabet.carrier
          (GGT.RelLetter.listVal C.rightSide)⁻¹ := by
      exact Nat.add_le_add_right
        (wordNorm_mul_le E.alphabet.symmetricGenerating _ _) _
    _ ≤ 2 * eps + 1 := by
      omega

/-- The same bound in distance-from-identity form. -/
theorem wordDist_replacementWord_adjoinRelatorPrefixes_le
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    wordDist (D.adjoinRelatorPrefixes W hsc).alphabet.carrier 1
      C.replacementWord.prod ≤ 2 * eps + 1 := by
  rw [wordDist_one_left]
  exact C.wordNorm_replacementWord_adjoinRelatorPrefixes_le hsc hrelator

/-! ## The quotient prefix shortcut -/

/-- Mapping to the prefix quotient preserves the uniform replacement bound. -/
theorem wordNorm_map_replacementWord_prefixQuotient_le
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (q : G →* Q) (hq : Function.Surjective q) :
    wordNorm (D.prefixQuotient W hsc q hq).alphabet.carrier
      (q C.replacementWord.prod) ≤ 2 * eps + 1 := by
  let E := D.adjoinRelatorPrefixes W hsc
  have hmap : wordNorm (E.mapSurjective q hq).alphabet.carrier
      (q C.replacementWord.prod) ≤
      wordNorm E.alphabet.carrier C.replacementWord.prod := by
    apply wordNorm_map_le E.alphabet.symmetricGenerating q
    intro x hx
    rw [GGT.RelGenSet.alphabet_carrier_mapSurjective]
    exact ⟨x, hx, rfl⟩
  exact le_trans hmap
    (C.wordNorm_replacementWord_adjoinRelatorPrefixes_le hsc hrelator)

/-- If the cell relator dies in the quotient, the selected exterior boundary
arc has prefix-quotient norm at most `2 * eps + 1`. -/
theorem wordNorm_map_boundaryArc_prefixQuotient_le
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (q : G →* Q) (hq : Function.Surjective q)
    (hkill : q (GGT.RelLetter.listVal relator) = 1) :
    wordNorm (D.prefixQuotient W hsc q hq).alphabet.carrier
      (q C.boundaryArc.prod) ≤ 2 * eps + 1 := by
  rw [← C.map_replacementWord_prod_eq_boundaryArc_prod q hkill]
  exact C.wordNorm_map_replacementWord_prefixQuotient_le
    hsc hrelator q hq

/-- Translated endpoint form of the quotient shortcut. -/
theorem wordDist_mul_map_boundaryArc_prefixQuotient_le
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (hrelator : relator ∈ W)
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (q : G →* Q) (hq : Function.Surjective q)
    (hkill : q (GGT.RelLetter.listVal relator) = 1) (x : Q) :
    wordDist (D.prefixQuotient W hsc q hq).alphabet.carrier x
      (x * q C.boundaryArc.prod) ≤ 2 * eps + 1 := by
  have htranslate := wordDist_left_invariant
    (D.prefixQuotient W hsc q hq).alphabet.carrier x 1
      (q C.boundaryArc.prod)
  have hbound := C.wordNorm_map_boundaryArc_prefixQuotient_le
    hsc hrelator q hq hkill
  calc
    wordDist (D.prefixQuotient W hsc q hq).alphabet.carrier x
        (x * q C.boundaryArc.prod) =
        wordDist (D.prefixQuotient W hsc q hq).alphabet.carrier 1
          (q C.boundaryArc.prod) := by
      simpa only [mul_one] using htranslate
    _ = wordNorm (D.prefixQuotient W hsc q hq).alphabet.carrier
          (q C.boundaryArc.prod) :=
      wordDist_one_left _ _
    _ ≤ 2 * eps + 1 := hbound

end RelativeBoundaryContiguity
end HullSC
end GroupApproximation
