import GroupApproximation.GGT.KazhdanHypTorsionCriterion

/-!
# The route without the quadrangle: girth-`8` tables and a rational certificate

`GGT/KazhdanHypTable.lean` states the route to `Hyperbolic.SharpExistence`
over `TableChecks`, whose last five clauses ask that the presentation link be
the incidence graph of a generalized quadrangle of order `q ≥ 7`.  That
hypothesis is now known to have no witness in the literature: every published
triangle presentation with a generalized-quadrangle link is over `GQ(2,2)`
(Vdovina, *Triangular hyperbolic buildings*, C. R. Acad. Sci. Paris 342 (2005);
Carbone--Kangaslampi--Vdovina, arXiv:1107.3690, which classifies exactly that
case; the accompanying search program searches "triangle presentations for a
one-vertex polyhedron having the smallest thick generalized quadrangle `GQ(2,2)`
as the vertex-link"), and `GQ(2,2)` has `kappa = 1/3`, below Zuk's threshold.
Chinyere--Williams (arXiv:2105.06204) classify the cyclic presentations whose
star-graph components are generalized polygons and find that "only generalized
triangles (i.e. incidence graphs of projective planes) and regular complete
bipartite graphs arise".

So the quadrangle is a *sufficient* source of a spectral gap and not a
necessary one, and the route should not be stated over it.  This module states
it over what the machine actually consumes:

* `GirthEightChecks T d` --- the link-agnostic finite checks: a positive table
  whose link is `d`-regular, simple, and has no four-cycle and no six-cycle.
  These are the `C(3)`-`T(8)` conditions and nothing else;
  `girthEightChecks_of_tableChecks` shows a quadrangle table has them.
* `GirthEightHyperbolicity`, `GirthEightInfinite`, `GirthEightTorsionFree` ---
  the three geometric residuals, restated over those checks.  Each implies its
  quadrangle-specific counterpart in `GGT/KazhdanHypTable.lean`, so nothing
  downstream is lost by moving to them.
* `TriangularKazhdanWitness` --- the sharpest form of what a witness must be:
  a triangular presentation, a regular link, a rational Gram factor clearing
  `1/2`, and a group that is infinite, torsion-free and hyperbolic.  No
  quadrangle, no girth clause, no order `q`.
  `sharpExistence_of_triangularKazhdanWitness` is the reduction, and
  `triangularKazhdanWitness_of_checkedTableWitness` checks that the quadrangle
  route is the special case it was meant to be.

Property `(T)` is discharged inside the reduction by
`hasKazhdanPropertyT_of_kgonChecks_three`, which needs the regularity and the
Gram factor and nothing about the link's combinatorial type.  The girth clauses
appear only where they are actually used --- as the hypothesis of the
`C(3)`-`T(8)` geometry --- and the spectral clause appears only as the rational
identity the Garland certificate consumes.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace KazhdanHyp

section Checks

variable {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-! ## The link-agnostic checks -/

/-- **The `C(3)`-`T(8)` checks on a triangle table**, with no reference to a
generalized quadrangle: the table is positive, its link is `d`-regular and
simple --- which is `C(3)`, by `corner_unique_of_linkSimple` --- and the link
has no four-cycle and no six-cycle, which for a simple bipartite graph is girth
at least `8`, that is `T(8)`.

Every clause is a count of natural numbers, so the predicate is decidable; and
by `no_cube_of_linkSimple` a table passing it also satisfies the
Kangaslampi--Vdovina torsion criterion. -/
def GirthEightChecks
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ) : Prop :=
  (∀ j k, (T j k).2 = true) ∧
  (∀ u, TriangularHodgeLayer.degree T u = d) ∧
  (∀ u v, TriangularHodgeLayer.adjacencyCount T u v ≤ 1) ∧
  (∀ v v', v ≠ v' →
    (∑ u, TriangularHodgeLayer.adjacencyCount T u v *
      TriangularHodgeLayer.adjacencyCount T u v') ≤ 1) ∧
  (∀ v v', TriangularHodgeLayer.adjacencyCount T v v' = 0 →
    (∑ a, ∑ b, TriangularHodgeLayer.adjacencyCount T v a *
      TriangularHodgeLayer.adjacencyCount T a b *
      TriangularHodgeLayer.adjacencyCount T b v') ≤ 1)

/-- A quadrangle table passes the link-agnostic checks: they are five of its
twelve clauses. -/
theorem girthEightChecks_of_tableChecks
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {q : ℕ}
    (h : TableChecks T q) : GirthEightChecks T (q + 1) :=
  ⟨h.2.1, h.regular, h.simple, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- The link of a checked table is regular; extracted for the assembly. -/
theorem GirthEightChecks.regular
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (h : GirthEightChecks T d) : ∀ u, TriangularHodgeLayer.degree T u = d :=
  h.2.1

/-- The link of a checked table is simple. -/
theorem GirthEightChecks.simple
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (h : GirthEightChecks T d) :
    ∀ u v, TriangularHodgeLayer.adjacencyCount T u v ≤ 1 :=
  h.2.2.1

/-- A table passing the link-agnostic checks satisfies the
Kangaslampi--Vdovina torsion criterion, by `no_cube_of_linkSimple`. -/
theorem GirthEightChecks.noCube
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (h : GirthEightChecks T d) (j : TriangleIndex) :
    ¬ (T j 0 = T j 1 ∧ T j 1 = T j 2) :=
  no_cube_of_linkSimple T h.simple j

end Checks

/-! ## The three geometric residuals, without the quadrangle -/

/-- **Hyperbolicity from `C(3)`-`T(8)`.**  `1/3 + 1/8 < 1/2` puts a girth-`8`
triangular presentation in the strictly hyperbolic small-cancellation band.
Not proved here: what is missing is a van Kampen diagram theory for the
non-metric conditions.  `Algebra/HyperbolicSlimFourPoint.lean` supplies the
last step of any such proof --- slim triangles give the repository's four-point
definition --- so what remains is the isoperimetric half. -/
def GirthEightHyperbolicity : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
    GirthEightChecks T d →
      Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T)

/-- **Infiniteness from `C(3)`-`T(8)`.**  Greendlinger's lemma for the
non-metric conditions gives it; not proved here, for the same reason. -/
def GirthEightInfinite : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
    GirthEightChecks T d → Infinite (TriangularHodgeLayer.Presented T)

/-- **Torsion-freeness from `C(3)`-`T(8)`.**  The criterion that separates the
torsion-free tables from the others --- no triangle with three equal letters ---
is a consequence of the simplicity clause (`GirthEightChecks.noCube`), so no
extra hypothesis appears here either; see
`GGT/KazhdanHypTorsionCriterion.lean`. -/
def GirthEightTorsionFree : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
    GirthEightChecks T d → IsPowerTorsionFree (TriangularHodgeLayer.Presented T)

/-! ## Nothing downstream is lost -/

/-- The quadrangle-specific hyperbolicity residual follows. -/
theorem cThreeTEightHyperbolicity_of_girthEight (h : GirthEightHyperbolicity) :
    CThreeTEightHyperbolicity := by
  intro Generator TriangleIndex fg dg ng ft dt T q hchecks
  exact h Generator TriangleIndex fg dg ng ft dt T (q + 1)
    (girthEightChecks_of_tableChecks hchecks)

/-- The quadrangle-specific infiniteness residual follows. -/
theorem cThreeTEightInfinite_of_girthEight (h : GirthEightInfinite) :
    CThreeTEightInfinite := by
  intro Generator TriangleIndex fg dg ng ft dt T q hchecks
  exact h Generator TriangleIndex fg dg ng ft dt T (q + 1)
    (girthEightChecks_of_tableChecks hchecks)

/-- The quadrangle-specific torsion-freeness residual, in its extra-free form,
follows. -/
theorem checkedTableTorsionFree_of_girthEight (h : GirthEightTorsionFree) :
    CheckedTableTorsionFree := by
  intro Generator TriangleIndex fg dg ng ft dt T q hchecks
  exact h Generator TriangleIndex fg dg ng ft dt T (q + 1)
    (girthEightChecks_of_tableChecks hchecks)

/-! ## The sharpest form of the obligation -/

/-- **What a witness must be, with nothing quadrangular left in it.**  A
triangular presentation whose link is `d`-regular, a rational Gram factor
certifying a spectral gap above `1/2`, and a group that is infinite,
torsion-free and hyperbolic.

The first two clauses are finite rational checks on a table; the last three are
facts about the presented group.  Property `(T)` and finite presentation do not
appear: they are theorems about any table with the first two. -/
def TriangularKazhdanWitness : Prop :=
  ∃ (Generator TriangleIndex Row : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex) (_ : Fintype Row)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ) (gap : ℚ)
    (rows : Row → Generator × Bool → ℚ),
    (∀ u, TriangularHodgeLayer.degree T u = d) ∧
      LinkCertificateChecks_kgon 3
        (fun u v => (TriangularHodgeLayer.adjacencyCount T u v : ℚ)) (d : ℚ) gap
        (1 / 2) rows ∧
      Infinite (TriangularHodgeLayer.Presented T) ∧
      IsPowerTorsionFree (TriangularHodgeLayer.Presented T) ∧
      Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T)

/-- **`SharpExistence` from the sharpest form.**  Property `(T)` comes from the
Garland certificate of `Kazhdan/TriangularHodgeLayer.lean` fed with the Gram
rows, and finite presentation from the presentation itself. -/
theorem sharpExistence_of_triangularKazhdanWitness (h : TriangularKazhdanWitness) :
    Hyperbolic.SharpExistence := by
  obtain ⟨Generator, TriangleIndex, Row, fg, dg, ng, ft, dt, fr, T, d, gap, rows,
    hdeg, hcert, hinf, htf, hhyp⟩ := h
  exact ⟨TriangularHodgeLayer.Presented T, inferInstance, hinf, inferInstance, htf,
    hhyp, hasKazhdanPropertyT_of_kgonChecks_three T d gap rows hdeg hcert⟩

/-- **The quadrangle route is the special case it was meant to be.**  A checked
quadrangle table supplies the regular link and, through the spectral bridge and
the two completed squares, the Gram factor. -/
theorem triangularKazhdanWitness_of_checkedTableWitness (h : CheckedTableWitness) :
    TriangularKazhdanWitness := by
  obtain ⟨Generator, TriangleIndex, fg, dg, ng, ft, dt, T, q, hchecks, hinf, htf, hhyp⟩ := h
  obtain ⟨Q, hadj, hdegval⟩ :=
    quadrangleDataOfChecks Generator TriangleIndex fg dg ng ft dt T q hchecks
  have hdq : ((q + 1 : ℕ) : ℚ) = Q.deg := by
    rw [← hdegval]
    push_cast; ring
  exact ⟨Generator, TriangleIndex, QuadRow (Generator × Bool), fg, dg, ng, ft, dt,
    inferInstance, T, q + 1, Q.gapValue, Q.gramRow, hchecks.regular,
    QuadrangleLinkData.linkCertificateChecks_kgon_of_quadrangle T Q (q + 1) hdq hadj,
    hinf, htf, hhyp⟩

end KazhdanHyp
end GroupApproximation
