import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExteriorLinked
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExteriorTwoGon
import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# The faces of `Φ'_M` that hold a relator cell

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "For any distinguished
system of ε-contiguity subdiagrams `M` in `∆`, the graph `Φ_M` is simple and inside every 2-gon of
`Φ'_M`, there is a vertex of `Φ_M`."  With the vertices `O_i` merged into one outer vertex `O`
(`Estimating/OsinAppendixEulerExterior.lean`), a two-gon of `Φ'_M` holds a corner of the sections
in its gap at `O` (C4 of the Lemma 9.3 count), holds a vertex of `Φ_M` (C5, this module), or is
empty (C6, `EmptyTwoGonInput`).

Take the regions `C = linkedComponentO E a₀` linked to an exterior region `a₀`, and their graph
`phiMapO family C`.  A face of it **holds a relator cell** (`RegionCandidate.HoldsCellO`) when its
face class reaches a dart of a relator cell that is not an end of `C`.  The face class advances
around the faces of the dual of the collapsed map and crosses the edges that are not retained
(`CombMap.FaceClassStep`, `GGT/VanKampen/CombMapRestrictionFaceClasses.lean`).

`CellFaceCountInput` states C5 as a count:

  `|E| + 3 · #{faces holding a cell} ≤ |C| + 3 · #{relator cells that are not ends of C}`.

By `CombMap.IsRestriction.faceOf_eq_of_faceClass` two different faces hold disjoint sets of cells.
A region outside `C` has both ends among the cells held by one face, and `card_le_of_endpoints`
bounds the regions on the cells `X` held by one face by `3(|X| − 1)`.  With the Euler count
`card_add_six_le_linkedComponentO`, `|C| + 6 ≤ 3(1 + #{ends of C}) + t`, and
`t ≤ r + #{faces holding a cell}` from C3, C4 and C6, the count gives `|E| ≤ 3(n + r − 1)`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w}

namespace Embedded.RegionCandidate

/-- **A face of `Φ'_M` holds a relator cell** that is not an end of the selected regions `E`: from
a retained dart of the face, advancing around the faces of the dual of the collapsed map and
crossing edges that are not retained reaches a dart of the cell. -/
def HoldsCellO {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} (family E : Finset (RegionCandidate D eps Delta))
    (f : (phiMapO family E).Face) : Prop :=
  ∃ i : Fin Delta.rCellCount, some i ∉ endCellsO E ∧
    ∃ d : (phiMapO family E).Dart, (phiMapO family E).faceOf d = f ∧
      ∃ x : (collapsedMap family).dual.Dart,
        Relation.EqvGen (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E))
          d.1 x ∧ Delta.toCombMap.faceOf x.1 = (cell Delta i).face

end Embedded.RegionCandidate

open scoped Classical in
/-- **C5 of Osin's Lemma 9.3: the faces of `Φ'_M` that hold a relator cell.**  Take regions `E`
carrying the data of `Φ'_M`, no two of them joining the same two cells, and an exterior region
`a₀ ∈ E` with its component `C = linkedComponentO E a₀`.  Then `|E|`, plus three for each face of
`phiMapO family C` that holds a relator cell, is at most `|C|` plus three times the number of
relator cells that are not ends of `C`. -/
def CellFaceCountInput (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (family E : Finset (RegionCandidate D eps Delta)),
    RegionCandidate.ExtPhiData family E →
    (∀ a ∈ E, ∀ b ∈ E, a ≠ b → ∀ i j : Fin Delta.rCellCount,
      a.JoinsCells i j → b.JoinsCells i j → False) →
    ∀ a₀ ∈ E, a₀.2.target = none →
      E.card +
          3 * (Finset.univ.filter fun f :
            (RegionCandidate.phiMapO family (RegionCandidate.linkedComponentO E a₀)).Face =>
              RegionCandidate.HoldsCellO family (RegionCandidate.linkedComponentO E a₀) f).card ≤
        (RegionCandidate.linkedComponentO E a₀).card +
          3 * (Finset.univ.filter fun i : Fin Delta.rCellCount =>
            some i ∉ RegionCandidate.endCellsO (RegionCandidate.linkedComponentO E a₀)).card

end GroupApproximation.GGT.VanKampen
