import GroupApproximation.GGT.DGOProposition414TargetTransport
import GroupApproximation.GGT.DGOAssemblyCharge

/-!
# Canonical open cut paths on the balanced arcs

The cuts stored in `BalancedSplitData` certify the two closed half-polygons,
but interval surgery needs named corners on the inherited *open* arcs.  This
file reconstructs those cuts canonically from the refined original cut.  The
first arc is an ordinary `arcWord`; the second is the wrapped suffix--prefix
arc.  Neither arc is required to close.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The inherited word on the first balanced arc, without the return chord. -/
def firstArc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    List (RelLetter G Λ) :=
  arcWord P.word B.refinedCut (B.firstSide + 1) (B.secondSide + 2)

/-- The inherited wrapped word on the second balanced arc, without the chord. -/
def secondArc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    List (RelLetter G Λ) :=
  P.word.drop B.secondVertex ++ P.word.take B.firstVertex

/-- The canonical side cut on the first inherited arc. -/
def firstArcCut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : ℕ → ℕ :=
  fun s => B.refinedCut (B.firstSide + 1 + s) -
    B.refinedCut (B.firstSide + 1)

/-- The canonical side cut on the wrapped second inherited arc. -/
def secondArcCut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : ℕ → ℕ :=
  appendCut
    (appendCut
      (fun s => B.refinedCut (B.secondSide + 2 + s) -
        B.refinedCut (B.secondSide + 2))
      (n + 2 - (B.secondSide + 2)) B.refinedCut)
    ((n + 2 - (B.secondSide + 2)) + (B.firstSide + 1)) (fun s => s)

private theorem refinedPolygonCut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    IsPolygonCut (n + 2) P.word B.refinedCut :=
  isPolygonCut_splitPair P.polygonCut B.side_order B.secondSide_lt
    B.firstVertex_mem.1 B.firstVertex_mem.2 B.secondVertex_mem.1
    B.secondVertex_mem.2

/-- The first inherited arc has its exact canonical open cut. -/
theorem firstArc_isCutPath
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    IsCutPath D (b : ℝ) (B.secondSide - B.firstSide + 1) B.firstBase
      B.firstArc B.firstArcCut := by
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  have hcount : B.secondSide + 2 - (B.firstSide + 1) =
      B.secondSide - B.firstSide + 1 := by omega
  refine
    { letters := ?_
      cut := ?_ }
  · intro x hx
    exact P.letters x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · change IsPolygonCut (B.secondSide - B.firstSide + 1)
      (arcWord P.word B.refinedCut (B.firstSide + 1) (B.secondSide + 2))
      (fun s => B.refinedCut (B.firstSide + 1 + s) -
        B.refinedCut (B.firstSide + 1))
    simpa only [hcount] using
      isPolygonCut_arcWord B.refinedPolygonCut
        (by omega : B.firstSide + 1 ≤ B.secondSide + 2)
        (by omega : B.secondSide + 2 ≤ n + 2)

/-- The wrapped second inherited arc has its exact canonical open cut. -/
theorem secondArc_isCutPath
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    IsCutPath D (b : ℝ) ((n - B.secondSide) + B.firstSide + 1)
      B.secondBase B.secondArc B.secondArcCut := by
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hcountTail : n + 2 - (B.secondSide + 2) = n - B.secondSide := by
    omega
  have hcount : (n + 2 - (B.secondSide + 2)) + (B.firstSide + 1) =
      (n - B.secondSide) + B.firstSide + 1 := by omega
  have hcut := isPolygonCut_secondHalf B.refinedPolygonCut
    (a := B.firstSide + 1) (b := B.secondSide + 2)
    (by omega : B.firstSide + 1 ≤ n + 2)
    (by omega : B.secondSide + 2 ≤ n + 2) ([] : List (RelLetter G Λ))
  refine
    { letters := ?_
      cut := ?_ }
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact P.letters x (List.mem_of_mem_drop hx)
    · exact P.letters x (List.mem_of_mem_take hx)
  · simpa only [secondArc, secondArcCut, secondHalf, List.append_nil,
      List.length_nil, Nat.add_zero, hleft, hright, hcountTail, hcount,
      Nat.add_assoc] using hcut

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
