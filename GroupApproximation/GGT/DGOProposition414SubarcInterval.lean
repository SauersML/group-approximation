import GroupApproximation.GGT.DGOProposition414HalfCutPath
import GroupApproximation.GGT.DGOProposition414OrientedSegment

/-!
# Producing one chord interval from a canonical inherited subarc

This is the exact adapter from an open parent cut path to
`AuxiliaryIntervalOnChord`.  The arc cut and its off-target quasigeodesicity
are derived by restriction; callers provide only endpoint, target, and
component geometry.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Restrict an inherited canonical cut path and package it as one raw
auxiliary interval on the common chord. -/
def auxiliaryIntervalOnChord_of_subarc
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (b : ℕ)
    {parentSides : ℕ} {parentBase : G}
    {parentWord : List (RelLetter G Λ)} {parentCut : ℕ → ℕ}
    (parentPath : IsCutPath D (b : ℝ) parentSides parentBase
      parentWord parentCut)
    (parentTarget : Finset ℕ)
    (parentQuasi : ∀ s : ℕ, s < parentSides → s ∉ parentTarget →
      ∀ p q : ℕ, parentCut s ≤ p → p ≤ q → q ≤ parentCut (s + 1) →
      ((q - p : ℕ) : ℝ) - b ≤
        ((wordDist D.alphabet.carrier
          (vertex parentBase parentWord p) (vertex parentBase parentWord q) : ℕ) : ℝ))
    (firstSide lastSide : ℕ) (hside : firstSide ≤ lastSide)
    (hlast : lastSide ≤ parentSides)
    (chordBase chordEnd : G) (globalChord : List (RelLetter G Λ))
    (globalGeodesic : IsGeodesicWord D chordBase chordEnd globalChord)
    (chordStart chordFinish : ℕ)
    (chordStart_le : chordStart ≤ globalChord.length)
    (chordFinish_le : chordFinish ≤ globalChord.length)
    (left right : List (RelLetter G Λ))
    (leftLetters : ∀ x ∈ left, D.IsLetter x)
    (rightLetters : ∀ x ∈ right, D.IsLetter x)
    (arcBase : vertex chordBase globalChord chordFinish *
        RelLetter.listVal (revWord left) =
      vertex parentBase parentWord (parentCut firstSide))
    (prefix_endpoint :
      vertex chordBase globalChord chordFinish *
          RelLetter.listVal
            ((revWord left ++ arcWord parentWord parentCut firstSide lastSide) ++
              right) =
        vertex chordBase globalChord chordStart)
    (localTarget : Finset ℕ) (label : ℕ → Λ)
    (target_reflect : ∀ r : ℕ, r < lastSide - firstSide →
      firstSide + r ∈ parentTarget → left.length + r ∈ localTarget)
    (localTarget_lt : ∀ s ∈ localTarget,
      s < left.length + (lastSide - firstSide) + right.length +
        (orientedSegment globalChord chordStart chordFinish).length)
    (localTarget_edge : ∀ s ∈ localTarget,
      auxiliaryCycleCut left (lastSide - firstSide)
          (fun r => parentCut (firstSide + r) - parentCut firstSide) right
          (s + 1) =
        auxiliaryCycleCut left (lastSide - firstSide)
          (fun r => parentCut (firstSide + r) - parentCut firstSide) right s + 1)
    (components : AuxiliaryCycleComponentConfiguration D
      (vertex chordBase globalChord chordFinish) left
      (arcWord parentWord parentCut firstSide lastSide) right
      (orientedSegment globalChord chordStart chordFinish)
      (lastSide - firstSide)
      (fun r => parentCut (firstSide + r) - parentCut firstSide)
      (localTarget ∪ auxiliaryCycleConnectorTarget left right
        (lastSide - firstSide)) label) :
    AuxiliaryIntervalOnChord D hsymm b chordBase chordEnd globalChord
      globalGeodesic := by
  let restricted := IsCutPath.arcWord parentPath hside hlast
  refine
    { chordStart := chordStart
      chordFinish := chordFinish
      chordStart_le := chordStart_le
      chordFinish_le := chordFinish_le
      left := left
      arc := arcWord parentWord parentCut firstSide lastSide
      right := right
      arcSides := lastSide - firstSide
      arcCut := fun r => parentCut (firstSide + r) - parentCut firstSide
      arcPolygon :=
        { letters := restricted.letters
          cut := restricted.cut }
      leftLetters := leftLetters
      rightLetters := rightLetters
      prefix_endpoint := prefix_endpoint
      localTarget := localTarget
      label := label
      arcQuasi := ?_
      localTarget_lt := localTarget_lt
      localTarget_edge := localTarget_edge
      components := components }
  intro r hr hrTarget p q hp hpq hq
  have hrestricted := IsCutPath.arcWord_quasi parentPath parentTarget
    parentQuasi hside hlast localTarget target_reflect r hr hrTarget
      p q hp hpq hq
  simpa only [arcBase] using hrestricted

end DGOProposition414
end GGT
end GroupApproximation
