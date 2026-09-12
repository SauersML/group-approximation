import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceLeavittClosure

/-!
# Composition of the printed root-detection sentences

This file supplies the sentence names still absent from census rows 233--245.
Rows 235--239, 241, and 245 are imported from `SentenceLeavittClosure`; their
proof bodies are not duplicated here.  The final declaration records the exact
root-detection endpoint obtained by the manuscript's diagonal/sparse/dense
case split.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u v

/-- **Sentence 233.**  Nonzero coefficients admit the asymmetric separation
pair used in the dense commutator case. -/
theorem manuscriptSentence233_coefficientSeparation
    {S : Type u} [Ring S] (L : LeavittFamily S)
    (hdivide : ∀ z : S, z ≠ 0 → ∃ c d : S, c * z * d = 1)
    {r s : S} (hr : r ≠ 0) (hs : s ≠ 0) :
    ∃ a b : S, a * r * b = 0 ∧ b * s * a * r ≠ 0 :=
  exists_annihilate_preserve_reverse L hdivide hr hs

/-- **Sentence 234.**  Every coefficient has a zero sandwich whose reversed
product remains nonzero. -/
theorem manuscriptSentence234_reversingZeroProduct
    {S : Type u} [Ring S] [Nontrivial S] (L : LeavittFamily S)
    (hdivide : ∀ z : S, z ≠ 0 → ∃ c d : S, c * z * d = 1)
    (w : S) :
    ∃ x y : S, x * w * y = 0 ∧ y * x ≠ 0 :=
  exists_reversing_zero_product L hdivide w

/-- **Sentence 240.**  Under the four displayed sandwich identities, the
printed definitions of `a` and `b` give `arb=0`, while `bsar=0` would force
the forbidden equation `yx=0`. -/
theorem manuscriptSentence240_explicitSeparationConclusion
    {S : Type u} [Ring S]
    {r s cr dr ed fd es fs et ft x y : S}
    (hcr : cr * r * dr = 1) (hdf : ed * dr * fd = 1)
    (hsf : es * s * fs = 1) (htf : et * (cr * r) * ft = 1)
    (hxy : x * (et * fd) * y = 0) (hyx : y * x ≠ 0) :
    let a := fs * x * et * cr
    let b := dr * fd * y * es
    a * r * b = 0 ∧ b * s * a * r ≠ 0 :=
  manuscript_coefficient_separation_explicit hcr hdf hsf htf hxy hyx

/-- **Sentence 242.**  The inverse of an invertible diagonal matrix is
diagonal, over the manuscript's possibly noncommutative coefficient ring. -/
theorem manuscriptSentence242_inverseOfDiagonal_isDiagonal
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (g : (Matrix ι ι S)ˣ)
    (hdiag : ∀ p q : ι, p ≠ q → (g : Matrix ι ι S) p q = 0) :
    ∀ p q : ι, p ≠ q →
      (((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) p q) = 0 := by
  intro p q hpq
  exact matrixUnit_inv_offDiag_eq_zero g hdiag hpq

/-- **Sentence 243.**  Trivial central coefficient units make the centre of
the elementary group trivial.  Combined with generation by elementary roots,
this is precisely the printed exclusion of a nonidentity diagonal element
commuting with every root. -/
theorem manuscriptSentence243_elementaryCenter_eq_bot
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] [Ring S]
    (hcentral : ∀ z : Sˣ,
      (∀ y : S, (z : S) * y = y * (z : S)) → z = 1) :
    Subgroup.center (elementaryGroup ι S) = ⊥ :=
  ElementarySimplicity.center_elementaryGroup_eq_bot_of_units hcentral

/-- **Sentence 244.**  In the diagonal branch, some elementary root line is
moved to the same line with a different coefficient; its commutator with the
normal element is therefore a nonzero elementary root in the subgroup. -/
theorem manuscriptSentence244_diagonalBranch_extractsRoot
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (hcard : 3 ≤ Fintype.card ι)
    (hcentral : ∀ z : Sˣ,
      (∀ y : S, (z : S) * y = y * (z : S)) → z = 1)
    (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    {g : elementaryGroup ι S} (hg : g ∈ N) (hgne : g ≠ 1)
    (hdiag : ∀ p q : ι, p ≠ q →
      ElementarySimplicity.elMat g p q = 0) :
    ∃ (i j : ι) (hij : i ≠ j) (a : S),
      a ≠ 0 ∧ elGen i j hij a ∈ N :=
  exists_elGen_mem_of_diagonal hcard hcentral N hg hgne hdiag

/-- **Rows 233--245, composed.**  For the exact rank-twelve binary Leavitt
group, the printed coefficient-separation and exhaustive case split detect a
nonzero elementary root in every nontrivial normal subgroup. -/
theorem manuscriptSentences233_245_rootDetection :
    ElementarySimplicity.RootDetection (Fin 12) RankTwelveEndpoint.R :=
  RankTwelveEndpoint.normalRootDetection

end OneSidedMFRadical
end Manuscript
end GroupApproximation
