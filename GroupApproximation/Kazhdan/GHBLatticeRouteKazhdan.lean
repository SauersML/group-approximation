import GroupApproximation.Kazhdan.GHBLatticeRoute
import GroupApproximation.Kazhdan.EJZAngleGHB
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Meta.AxiomGuard

/-!
# The lattice route through `GHB(7)`, with property (T) proved

`Kazhdan/GHBLatticeRoute` builds `Hyperbolic.LatticeRouteInput` and `Hyperbolic.SharpExistence`
from the Kac--Moody--Steinberg group `GHB(7)` over the open leaves `hconj`, `h3`, `h4`, `hhyp`,
`hT`.  The leaf `hT : HasKazhdanPropertyT.{0, 0} (GHB 7)` is `hasKazhdanPropertyT_ghb7`
(`Kazhdan/EJZAngleGHB`: Caprace--Conder--Kaluba--Witzel, arXiv:2011.09276, Theorem 1.3 at `p = 7`,
through the Ershov--Jaikin-Zapirain criterion, proved from the relators of `GHB(7)`).  This module
restates the route with `hT` removed; `hconj`, `h3`, `h4`, `hhyp` stay ordinary hypotheses.

`PrintedGHB7PropertyT` is the closed endpoint.  It asks for property (T) in both forms: the real
orthogonal form at representation universe `0`, which is the form `LatticeRouteInput.kazhdan` and
`SharpExistence` use, and the textbook complex-unitary form (`hasKazhdanPropertyT_iff_textbook`).

The non-MF manuscript names no `GHB(7)`.  `Hyperbolic.SharpExistence` is a repository statement,
not a printed sentence.
-/

namespace GroupApproximation
namespace KMSGroup
namespace GHBQuotient

/-- **`GHB(7)` has Kazhdan's property (T)** (CCKW Theorem 1.3 at `p = 7`).  Both forms are stated:
the real orthogonal form on Hilbert spaces in `Type` (`HasKazhdanPropertyT.{0, 0}`, used by
`Hyperbolic.LatticeRouteInput` and `Hyperbolic.SharpExistence`), and the textbook form with unitary
representations on complex Hilbert spaces (`HasKazhdanPropertyTComplex.{0, 0}`). -/
def PrintedGHB7PropertyT : Prop :=
  HasKazhdanPropertyT.{0, 0} (GHB 7) ∧ HasKazhdanPropertyTComplex.{0, 0} (GHB 7)

/-- `GHB(7)` has property (T), in both forms, with no literature input. -/
theorem printedGHB7PropertyT : PrintedGHB7PropertyT :=
  ⟨hasKazhdanPropertyT_ghb7, hasKazhdanPropertyT_iff_textbook.{0, 0}.mp hasKazhdanPropertyT_ghb7⟩

/-- **The lattice datum from `GHB(7)`**, with property (T) supplied by `hasKazhdanPropertyT_ghb7`.
The remaining open leaves are `hconj` (CCKW Theorem 3.1(ii), cyclic case), `h3`, `h4` (CCKW
Proposition 7.2 order bounds) and `hhyp` (CCKW Theorem 3.1(i)). -/
def ghb7KazhdanLatticeRouteInput (hconj : CCKWFiniteOrderConjugateIntoVertex)
    [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) :
    Hyperbolic.LatticeRouteInput :=
  ghb7LatticeRouteInput hconj h3 h4 hhyp hasKazhdanPropertyT_ghb7

/-- **`SharpExistence` from `GHB(7)`**, over `hconj`, `h3`, `h4`, `hhyp` only. -/
theorem sharpExistence_of_ghb7KazhdanLeaves (hconj : CCKWFiniteOrderConjugateIntoVertex)
    [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) :
    Hyperbolic.SharpExistence :=
  sharpExistence_of_ghb7Leaves hconj h3 h4 hhyp hasKazhdanPropertyT_ghb7

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.sharpExistence_of_ghb7KazhdanLeaves
#audit_closed_axioms GroupApproximation.KMSGroup.GHBQuotient.printedGHB7PropertyT
