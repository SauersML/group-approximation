import GroupApproximation.GGT.HullSCLemma44CellContiguity
import GroupApproximation.GGT.HullSCLemma44ExteriorArc

/-!
# Relative contiguity diagrams in Hull's Lemma 4.4

The old version of this module replaced Osin's planar estimating graph by an
outerplanar chord graph and replaced Lemma 9.7's single large exterior
contiguity arc by three interior pieces.  Neither replacement is the source
argument: the estimating graph is an arbitrary simple planar graph, and the
one-section conclusion is an exterior contiguity degree greater than
`1 - 13 * mu`.

The cell-to-cell labels are now represented by `Lemma44CellContiguity`, whose
published-piece property follows from least-area reducedness (Osin Lemma 4.3),
and the exterior output is `Lemma44LargeExteriorCell`.  The theorem below is
the exact final reduction consumed by the direct Lemma 9.7 construction.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- Failure of ball injectivity supplies a least-area oriented diagram.  A
source-faithful one-section Lemma 9.7 certificate for that diagram contradicts
the short geodesic exterior boundary. -/
theorem injOn_cayleyBall_of_largeExteriorCells
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (P : AuxiliaryPeripheralFamily A N S)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input P.rel W eps mu rho)
    (hmu : mu ≤ 1 / 52)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hgreendlinger : ∀ Z : Lemma44OrientedRelatorDiagram A.alphabet W R,
      Nonempty (Lemma44LargeExteriorCell P.rel W eps mu
        Z.toLemma44ReducedRelatorDiagram)) :
    Set.InjOn q (cayleyBall A.alphabet R) := by
  by_contra hnot
  obtain ⟨Z₀⟩ := exists_lemma44ReducedRelatorDiagram_of_not_injOn
    A.alphabet W R q hker hnot
  obtain ⟨Z⟩ := Z₀.exists_oriented hsc.toIsSmallCancellation
  obtain ⟨C⟩ := hgreendlinger Z
  exact false_of_lemma44LargeExteriorCell P
    Z.toLemma44ReducedRelatorDiagram hsc hmu hthreshold C

end HullSC
end GroupApproximation
