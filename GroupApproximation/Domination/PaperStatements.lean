import GroupApproximation.Domination.Comparison
import GroupApproximation.Domination.FixedDimension
import GroupApproximation.Domination.Irreducible
import GroupApproximation.Domination.JetDetector

/-!
# Paper-facing statements: quantitative radicals and dimension escape

This is the stable theorem interface for the domination/dimension-escape
paper.  It exposes only proved endpoints and keeps the remaining analytic
curve-selection bridge visible as a hypothesis where it has not yet been
formalized.

Credit boundary:

* Cartesian powers, tensor powers, conjugate doubling, complete reducibility,
  semialgebraic curve selection, truncated jets, and Mal'cev residual
  finiteness are classical inputs.
* Elek--Szabó receive credit for the standard sofic-to-hyperlinear embedding.
* The presentation-dependent linearization, finite-dimensional domination
  target, and irreducible dimension-escape synthesis are the paper-specific
  statements organized by this API.
-/

namespace GroupApproximation

variable (G : Type*) [Group G]

/-- Qualitative finite-action collapse is equivalent to a single linear
permutation-character domination constant. -/
theorem finiteActionCollapse_iff_linearPermutationDomination
    (R : Finset G) (w : G) :
    PermutationCharacterVanishesAtZero G R w ↔
      HasPermutationCharacterDomination G R w :=
  permutationCharacterVanishesAtZero_iff_hasDomination G R w

/-- Qualitative finite-dimensional character collapse is equivalent to a
single dimension-independent unitary-character domination constant. -/
theorem finiteDimensionalCollapse_iff_linearUnitaryDomination
    (R : Finset G) (w : G) :
    FDCharacterVanishesAtZero G R w ↔
      HasFDCharacterDomination G R w :=
  fdCharacterVanishesAtZero_iff_hasDomination G R w

/-- The exact permutation-matrix comparison, i.e. the predicate form of
`C_perm ≤ C_fd`. -/
theorem permutationDomination_of_unitaryDomination
    {R : Finset G} {w : G}
    (h : HasFDCharacterDomination G R w) :
    HasPermutationCharacterDomination G R w :=
  hasPermutationCharacterDomination_of_hasFDCharacterDomination h

/-- If all fixed matrix dimensions are controlled but the global constant is
infinite, bad representations can be chosen with dimensions tending to
infinity. -/
theorem obstruction_requires_matrixDimensionEscape
    {R : Finset G} {w : G}
    (hfixed : ∀ d, HasFDCharacterDominationInDimension G d R w)
    (hglobal : ¬ HasFDCharacterDomination G R w) :
    ∃ π : ℕ → FDUnitaryRepresentation G,
      IsFDDominationEscapingSequence G R w π ∧
      Filter.Tendsto (fun n ↦ Fintype.card (π n).carrier)
        Filter.atTop Filter.atTop :=
  obstruction_requires_dimensionEscape G hfixed hglobal

/-- Fixed-dimensional irreducible affine bounds control arbitrary total
dimension and multiplicity when all irreducible blocks have bounded degree. -/
theorem boundedIrreducibleDegree_linearDomination
    {D : ℕ} {R : Finset G} {w : G}
    (hfixed : ∀ d ≤ D,
      HasIrreducibleAffineDominationInDimension G d R w) :
    HasBoundedIrreducibleDegreeAffineDomination G D R w :=
  boundedIrreducibleDegree_affineDomination G hfixed

/-- Failure of global irreducible domination, despite every fixed-dimensional
bound, requires irreducible degrees tending to infinity. -/
theorem obstruction_requires_irreducibleDegreeEscape
    {R : Finset G} {w : G}
    (hfixed : ∀ d,
      HasIrreducibleAffineDominationInDimension G d R w)
    (hglobal : ¬ HasIrreducibleAffineDomination G R w) :
    ∃ π : ℕ → FDUnitaryRepresentation G,
      IsIrreducibleAffineEscapingSequence G R w π ∧
      Filter.Tendsto (fun n ↦ Fintype.card (π n).carrier)
        Filter.atTop Filter.atTop :=
  obstruction_requires_irreducibleDimensionEscape G hfixed hglobal

end GroupApproximation
