import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSubdivided
import GroupApproximation.Meta.AxiomGuard

/-!
# Euler's count for a subdivided graph with multiple edges

Osin's graph `Φ'_M` (arXiv:math/0411039v3, Appendix, just before Lemma 9.3) adds to `Φ_M` one
vertex for each section of `∂Δ`, and one edge through each selected region of a cell to a section.
A cell can have several regions to one section, so `Φ'_M` has multiple edges, and condition `(∗)`
asks only for a vertex of `Φ_M` inside every 2-gon.  In Lemma 9.3, "By (∗), every region of it
(except possibly for the outer one) has degree at least three", so the 2-gons enter the Euler count
through the faces of degree two.

`SubdividedMultigraph M ρ C` is `SubdividedGraph` (`Estimating/OsinAppendixEulerSubdivided.lean`)
without `noMultiple`.  This module states:

* `SubdividedMultigraphFaceStatement`: every face has degree at least four, and in a connected map
  with more than four darts a face of degree less than six is a two-gon
  (`SubdividedMultigraph.IsTwoGon`), two different regions joining the same two cells and
  consecutive in the rotations at both;
* `MidpointCountTwoGonStatement`: a planar map with `4m` darts, at most `c + m` vertices and every
  face of degree at least four has `m + 6 ≤ 3c + t`, where `t` is the number of faces of degree
  less than six;
* `EdgeBoundSubdividedMultigraphStatement`: the same count for a planar subdivided multigraph.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe v w z

variable (M : CombMap.{v})

/-- **A map subdividing every edge of a multigraph once**: `SubdividedGraph` without
`noMultiple`.  Darts based at cells carry the cell of their edge's cell end; darts based at
midpoints carry their region and the cell at the far end of their edge.  A midpoint holds the two
darts of one region, whose ends are different cells.  Two regions may join the same pair of
cells. -/
structure SubdividedMultigraph (ρ : Type w) (C : Type z) where
  /-- The darts based at cells; the others are based at midpoints. -/
  IsCellDart : M.Dart → Prop
  /-- The region of the edge carrying a dart. -/
  region : M.Dart → ρ
  /-- The cell at the cell end of the edge carrying a dart. -/
  endCell : M.Dart → C
  cellDart_alpha : ∀ d, IsCellDart (M.alpha d) ↔ ¬ IsCellDart d
  region_alpha : ∀ d, region (M.alpha d) = region d
  endCell_alpha : ∀ d, endCell (M.alpha d) = endCell d
  cellDart_of_vertex : ∀ d e, M.vertexOf d = M.vertexOf e → (IsCellDart d ↔ IsCellDart e)
  endCell_of_vertex : ∀ d e, IsCellDart d → IsCellDart e →
    M.vertexOf d = M.vertexOf e → endCell d = endCell e
  region_of_vertex : ∀ d e, ¬ IsCellDart d → ¬ IsCellDart e →
    M.vertexOf d = M.vertexOf e → region d = region e
  sigma_ne_of_midpoint : ∀ d, ¬ IsCellDart d → M.sigma d ≠ d
  endCell_ne : ∀ d e, ¬ IsCellDart d → ¬ IsCellDart e → region e = region d → d ≠ e →
    endCell d ≠ endCell e
  midpoint_two : ∀ d e x, ¬ IsCellDart d → ¬ IsCellDart e → ¬ IsCellDart x →
    region e = region d → region x = region d → d ≠ e → x = d ∨ x = e

variable {M}

/-- A subdivided graph is a subdivided multigraph. -/
def SubdividedGraph.toSubdividedMultigraph {ρ : Type w} {C : Type z}
    (S : SubdividedGraph M ρ C) : SubdividedMultigraph M ρ C :=
  { S with }

namespace SubdividedMultigraph

variable {ρ : Type w} {C : Type z} (S : SubdividedMultigraph M ρ C)

/-- **A two-gon**: a face through a cell dart `d` that closes after four steps and crosses two
different regions.  The region of `d` joins `S.endCell d` to `S.endCell (M.facePerm d)`, the region
of `M.facePerm (M.facePerm d)` joins them back, and the two are consecutive in the rotations at
both cells. -/
def IsTwoGon (f : M.Face) : Prop :=
  ∃ d : M.Dart, S.IsCellDart d ∧ M.faceOf d = f ∧
    M.facePerm (M.facePerm (M.facePerm (M.facePerm d))) = d ∧
      S.region (M.facePerm (M.facePerm d)) ≠ S.region d

end SubdividedMultigraph

/-- **The faces of a subdivided multigraph.**  Every face has degree at least four.  In a connected
map with more than four darts, a face of degree less than six is a two-gon. -/
def SubdividedMultigraphFaceStatement : Prop :=
  ∀ (M : CombMap.{v}) {ρ : Type w} {C : Type z} (S : SubdividedMultigraph M ρ C),
    (∀ f : M.Face, 4 ≤ M.faceDegree f) ∧
      (M.IsConnected → 4 < M.dartCount →
        ∀ f : M.Face, M.faceDegree f < 6 → S.IsTwoGon f)

/-- **Euler's count with two-gons.**  A planar map with `4m` darts, at most `c + m` vertices and
every face of degree at least four has `m + 6 ≤ 3c + t`, where `t` is the number of faces of
degree less than six. -/
def MidpointCountTwoGonStatement : Prop :=
  ∀ (M : CombMap.{v}), M.IsPlanar → ∀ c m : ℕ, M.dartCount = 4 * m →
    M.vertexCount ≤ c + m → (∀ f : M.Face, 4 ≤ M.faceDegree f) →
      m + 6 ≤ 3 * c + (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card

/-- **The edge bound of a subdivided multigraph**: `m` regions on `c` cells of a planar subdivided
multigraph with `t` faces of degree less than six give `m + 6 ≤ 3c + t`. -/
def EdgeBoundSubdividedMultigraphStatement : Prop :=
  ∀ (M : CombMap.{v}) {ρ : Type w} {C : Type z}, SubdividedMultigraph M ρ C → M.IsPlanar →
    ∀ c m : ℕ, M.dartCount = 4 * m → M.vertexCount ≤ c + m →
      m + 6 ≤ 3 * c + (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card

end GroupApproximation.GGT.VanKampen.CombMap
