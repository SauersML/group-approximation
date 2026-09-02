import GroupApproximation.GGT.DGOProposition414ChordComponentFieldWrapped

/-!
# Both Proposition 4.14 gap component families, from one residual seam

Three of the four component fields of `First/SecondGapComponentFamily` are now
theorems with no residual hypothesis: the inherited arc target, the left
connector and the right connector.  The fourth, the charged partner edge of the
opposite half, is a theorem except at one configuration, where the right
connector degenerates while the inherited arc is nonempty and the partner edge
opens the child chord.  This module assembles the four fields, so the family
half of the Proposition 4.14 producer is reduced to that single clause.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The first-half gap component family, from the residual charged arc seam
alone. -/
theorem firstGapComponentFamily_of_chordArcSeams
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hseam : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount) (s : ℕ),
      s ∈ B.firstGapChordSources j → FirstGapChordArcSeam B j s) :
    FirstGapComponentFamily B where
  arcComponent := fun j s hs => B.firstGapArcComponentField j s hs
  chordComponent := fun j s hs =>
    B.firstGapChordComponentField j s hs (hseam j s hs)
  leftComponent := fun j r hr => B.firstGapLeftComponentField j r hr
  rightComponent := fun j r hr => B.firstGap_rightComponent j r hr

/-- The wrapped gap component family, from the residual charged arc seam
alone. -/
theorem secondGapComponentFamily_of_chordArcSeams
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hseam : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount) (s : ℕ),
      s ∈ B.secondGapChordSources j → SecondGapChordArcSeam B j s) :
    SecondGapComponentFamily B where
  arcComponent := fun j s hs => B.secondGapArcComponentField j s hs
  chordComponent := fun j s hs =>
    B.secondGapChordComponentField j s hs (hseam j s hs)
  leftComponent := fun j r hr => B.secondGapLeftComponentField j r hr
  rightComponent := fun j r hr => B.secondGap_rightComponent j r hr

/-- Both families at once, in the `Nonempty` shape the Proposition 4.14
producer consumes. -/
theorem exists_gapComponentFamilies_of_chordArcSeams
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hfirst : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount) (s : ℕ),
      s ∈ B.firstGapChordSources j → FirstGapChordArcSeam B j s)
    (hsecond : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount) (s : ℕ),
      s ∈ B.secondGapChordSources j → SecondGapChordArcSeam B j s) :
    Nonempty (FirstGapComponentFamily B) ∧
      Nonempty (SecondGapComponentFamily B) :=
  ⟨⟨B.firstGapComponentFamily_of_chordArcSeams hfirst⟩,
    ⟨B.secondGapComponentFamily_of_chordArcSeams hsecond⟩⟩

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
