import GroupApproximation.GGT.DGOProposition414BrokenAssignment

/-!
# Distinguished-component placement in the balanced halves

This file fixes the actual coordinate systems used by the two component
surgery halves.  The first half reads the selected polygon arc followed by the
reversed chord; the second reads the wrapped complementary arc followed by the
forward chord.  Accordingly a chord coordinate `y` occurs at
`arcLength + (L - 1 - y)` in the first half and at `arcLength + y` in the
second.

`BalancedSplitComponentPlacement` records the geometric placement of the
original distinguished components in those two concrete words.  Survival is
not a caller-chosen predicate: it is definitionally `IsIsolated` in the
corresponding half.  Its constructor theorem therefore feeds the canonical
broken filters directly into `exists_brokenHalfAssignment`.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

def refinedCut {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : ℕ → ℕ :=
  splitPairCut P.cut B.firstSide B.secondSide B.firstVertex B.secondVertex

def firstWord {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    List (RelLetter G Λ) :=
  firstHalf P.word B.refinedCut (B.firstSide + 1) (B.secondSide + 2) B.chord

def secondWord {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    List (RelLetter G Λ) :=
  secondHalf P.word B.refinedCut (B.firstSide + 1) (B.secondSide + 2) B.chord

def firstBase {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : G :=
  vertex P.basepoint P.word B.firstVertex

def secondBase {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : G :=
  vertex P.basepoint P.word B.secondVertex

def firstArcLength {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : ℕ :=
  B.secondVertex - B.firstVertex

def secondArcLength {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : ℕ :=
  (P.word.length - B.secondVertex) + B.firstVertex

/-- Absolute first-half position of original forward-chord coordinate `y`. -/
def firstChordPos {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (y : ℕ) : ℕ :=
  B.firstArcLength + (B.chord.length - 1 - y)

/-- Absolute second-half position of forward-chord coordinate `y`. -/
def secondChordPos {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (y : ℕ) : ℕ :=
  B.secondArcLength + y

end BalancedSplitData

/-- Placement and separation data produced by transporting the original
distinguished components into the two concrete balanced half words. -/
structure BalancedSplitComponentPlacement
    (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} (P : SumBoundInput D (b : ℝ) n) {k R : ℕ}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  firstTarget : Finset ℕ
  secondTarget : Finset ℕ
  target_disjoint : Disjoint firstTarget secondTarget
  target_cover : P.target = firstTarget ∪ secondTarget
  firstPos : ℕ → ℕ
  secondPos : ℕ → ℕ
  firstPos_injective : Set.InjOn firstPos (↑firstTarget : Set ℕ)
  secondPos_injective : Set.InjOn secondPos (↑secondTarget : Set ℕ)
  first_start : ∀ s ∈ firstTarget,
    IsCompStart (P.label s) B.firstWord (firstPos s)
  second_start : ∀ s ∈ secondTarget,
    IsCompStart (P.label s) B.secondWord (secondPos s)
  first_separated : ∀ s ∈ brokenSet firstTarget (fun t =>
      IsIsolated D.fam (P.label t) B.firstBase B.firstWord (firstPos t)),
    ∀ t ∈ brokenSet firstTarget (fun t =>
      IsIsolated D.fam (P.label t) B.firstBase B.firstWord (firstPos t)),
      P.label s = P.label t → firstPos s ≠ firstPos t →
      ¬ Connected D.fam (P.label s) B.firstBase B.firstWord
        (firstPos s) (firstPos t)
  second_separated : ∀ s ∈ brokenSet secondTarget (fun t =>
      IsIsolated D.fam (P.label t) B.secondBase B.secondWord (secondPos t)),
    ∀ t ∈ brokenSet secondTarget (fun t =>
      IsIsolated D.fam (P.label t) B.secondBase B.secondWord (secondPos t)),
      P.label s = P.label t → secondPos s ≠ secondPos t →
      ¬ Connected D.fam (P.label s) B.secondBase B.secondWord
        (secondPos s) (secondPos t)
  first_partner : ∀ s ∈ brokenSet firstTarget (fun t =>
      IsIsolated D.fam (P.label t) B.firstBase B.firstWord (firstPos t)),
    ∃ y : ℕ, y < B.chord.length ∧
      IsCompStart (P.label s) B.firstWord (B.firstChordPos y) ∧
      Connected D.fam (P.label s) B.firstBase B.firstWord
        (firstPos s) (B.firstChordPos y)
  second_partner : ∀ s ∈ brokenSet secondTarget (fun t =>
      IsIsolated D.fam (P.label t) B.secondBase B.secondWord (secondPos t)),
    ∃ y : ℕ, y < B.chord.length ∧
      IsCompStart (P.label s) B.secondWord (B.secondChordPos y) ∧
      Connected D.fam (P.label s) B.secondBase B.secondWord
        (secondPos s) (B.secondChordPos y)

namespace BalancedSplitComponentPlacement

def firstSurvives
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (C : BalancedSplitComponentPlacement D hsymm b hδ P B) (s : ℕ) : Prop :=
  IsIsolated D.fam (P.label s) B.firstBase B.firstWord (C.firstPos s)

def secondSurvives
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (C : BalancedSplitComponentPlacement D hsymm b hδ P B) (s : ℕ) : Prop :=
  IsIsolated D.fam (P.label s) B.secondBase B.secondWord (C.secondPos s)

/-- Construct the canonical broken assignments and two-half greedy index in
the actual balanced-half coordinate systems. -/
theorem exists_twoHalfBrokenAssignment
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (C : BalancedSplitComponentPlacement D hsymm b hδ P B) :
    Nonempty (TwoHalfBrokenAssignment D B.firstBase B.secondBase B.firstWord
      B.secondWord C.firstTarget C.secondTarget C.firstSurvives
      C.secondSurvives P.label C.firstPos C.secondPos B.chord.length
      B.firstChordPos B.secondChordPos) := by
  obtain ⟨first⟩ := exists_brokenHalfAssignment D B.firstBase B.firstWord
    C.firstTarget C.firstSurvives P.label C.firstPos B.chord.length
    B.firstChordPos C.firstPos_injective C.first_separated C.first_partner
  obtain ⟨second⟩ := exists_brokenHalfAssignment D B.secondBase B.secondWord
    C.secondTarget C.secondSurvives P.label C.secondPos B.chord.length
    B.secondChordPos C.secondPos_injective C.second_separated C.second_partner
  exact ⟨⟨first, second⟩⟩

end BalancedSplitComponentPlacement

end DGOProposition414
end GGT
end GroupApproximation
