import GroupApproximation.GGT.KazhdanHypQuadrangle

/-!
# The triangle table as a checkable object, and the `C(3)`-`T(8)` route

`GGT/KazhdanHypQuadrangle.lean` discharges property `(T)` for a one-vertex
triangular presentation whose link is the incidence graph of a generalized
quadrangle of order `q ≥ 7`.  Two clauses of `Hyperbolic.SharpExistence` remain:
hyperbolicity and torsion-freeness.  This module routes both through **non-metric
small cancellation** rather than through `CAT(-1)` geometry, which is what makes
them conditions on a finite table, and then packages the whole thing as a
predicate a computational lane can discharge by exhibiting bytes.

## `C(3)` and `T(8)` for a one-vertex triangle table

Let `T` be a family of triangles over a generator alphabet, all letters
positive, and let `R` be the symmetrized relator set.

**Pieces are single letters.**  A piece of length two is a pair of distinct
elements of `R` sharing a two-letter prefix, that is, two distinct corners of
the table with the same ordered pair of consecutive letters.  In the
presentation link that is a repeated edge: `directedAdjacencyCount` counts
exactly those corners, so two of them give an edge of multiplicity at least two.
**A simple link therefore forces every piece to have length one**, and a
length-three relator is then a product of exactly three pieces and of no fewer:
`C(3)` holds.  `corner_unique_of_linkSimple` below is that argument.

**`T(q)` is link girth `≥ q`.**  In a reduced van Kampen diagram an interior
vertex of degree `h` is a closed cycle of length `h` in the link, so the
condition that every interior vertex has degree at least `q` is exactly that the
link has girth at least `q`.  For a bipartite link --- which a positive table
always has, the two sides being the positive and the inverse letters --- girth
is even, so girth `≥ 7` and girth `≥ 8` coincide.

**The band.**  `C(p)`-`T(q)` is nonpositively curved when `1/p + 1/q ≤ 1/2`,
with the three Euclidean boundary cases `(6,3)`, `(4,4)`, `(3,6)`, and strictly
hyperbolic when the inequality is strict.  Here `1/3 + 1/8 = 11/24 < 1/2`, so a
girth-`8` link puts the group in the strictly hyperbolic band --- the same
inequality that `gromovLinkCondition 3 8` records on the geometric side, arriving
combinatorially instead.

## What this repository's small-cancellation machinery can and cannot say

It cannot say any of it, and the reason is structural rather than incidental.

`Sofic/SmallCancellationRouter.lean` carries `symmetrization`,
`normalClosure_symmetrization`, `IsPiece`, `GreendlingerConclusion` and
`GreendlingerConclusionSharp lam`; the seventy-odd `Sofic/Greendlinger*` modules
build the Dehn-algorithm route to the Greendlinger conclusion, whose rewriting
rule is "a symmetrized relator `r = u ++ v` with `2|u| > |r|` lets `u` be
replaced by `invRev v`".  Every one of those is the **metric** condition.  For a
relator of length three, `C'(λ)` needs pieces shorter than `3λ`, so a
single-letter piece already forces `λ > 1/3`: **no length-three presentation is
ever `C'(1/6)`, or `C'(λ)` for any `λ ≤ 1/3`,** and the entire Greendlinger
development is inapplicable by arithmetic, not by omission.

What is reusable is the hypothesis-free scaffolding: `symmetrization`,
`normalClosure_symmetrization` and `IsPiece` are exactly the vocabulary in which
`C(3)` has to be stated, and `corner_unique_of_linkSimple` below is the bridge
from the link table to that vocabulary.

`Sofic/OsinRelativeSmallCancellation.lean` proves a torsion theorem of the right
*shape* --- in a relative small-cancellation quotient every element of finite
order is conjugate into a peripheral subgroup, so torsion cannot appear from
nowhere --- but it is relative small cancellation over a free product, not an
absolute `C(3)`-`T(8)` presentation, and it does not apply here.

## Torsion-freeness is not a consequence of the link

This is the finding that changes the shape of the answer, and it is a deduction
rather than a citation.

Kangaslampi and Vdovina classify the one-vertex triangle tables whose link is
the smallest thick generalized quadrangle `GQ(2,2)` and find **23 torsion-free
groups and 168 torsion groups**, all with the same link.  The obvious candidate
criterion is "no relator is a proper power", which for a positive length-three
relator means "not all three letters equal".  But a relator `x x x` contributes
three corners with the same ordered pair, so it makes the link edge from `x` to
`x⁻¹` have multiplicity three; the incidence graph of `GQ(2,2)` is simple, so
**every one of the 191 tables already has no relator a proper power.**  The
proper-power criterion cannot be the discriminator, and torsion-freeness is not
implied by the link data.

Accordingly `TableTorsionFree` below is a hypothesis and not a conclusion, and
`TableChecks` deliberately does not pretend to imply it.  The criterion that
separates the 23 from the 168 is in the body of the Kangaslampi--Vdovina paper,
which I could not read; recovering it is the cheapest remaining literature task,
and it is what would turn `TableTorsionFree` into another decidable clause.

## The checkable table

`TableChecks T q` is a finite conjunction of decidable conditions on natural
numbers:

* every letter of every triangle is positive;
* the link is `(q+1)`-regular and simple;
* no triangle has all three letters equal;
* no four-cycle and no six-cycle in the link, which for a bipartite simple graph
  is girth `≥ 8`;
* the generator count is the point count `(q+1)(q²+1)` of the quadrangle;
* the collinearity table derived from the link is `q(q+1)`-regular, vanishes
  across the two sides, and satisfies the strongly regular identity with
  parameters `((q+1)(q²+1), q(q+1), q-1, q+1)`.

Everything is a finite count, so `TableChecks` is decidable, and
`sharpExistence_of_tableChecks` turns a table passing it --- together with the
three named statements this repository does not prove --- into
`Hyperbolic.SharpExistence`.  A computational lane then has to exhibit bytes and
nothing else.
-/

namespace GroupApproximation
namespace KazhdanHyp

/-! ## Pieces are single letters -/

/-- **A simple link forces distinct corners to carry distinct consecutive
pairs.**  This is the combinatorial content of `C(3)`: a piece of length two
would be two corners with the same ordered pair of consecutive letters, and
`directedAdjacencyCount` counts exactly those, so it would make the
corresponding link edge have multiplicity at least two. -/
theorem corner_unique_of_linkSimple
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (hsimple : ∀ u v, TriangularHodgeLayer.adjacencyCount T u v ≤ 1)
    {p p' : TriangleIndex × Fin 3}
    (h1 : T p.1 p.2 = T p'.1 p'.2)
    (h2 : T p.1 (TriangularHodgeLayer.nextCorner p.2)
        = T p'.1 (TriangularHodgeLayer.nextCorner p'.2)) :
    p = p' := by
  classical
  by_contra hne
  set u := T p.1 p.2 with hu
  set v := TriangularHodgeLayer.inverseSigned
    (T p.1 (TriangularHodgeLayer.nextCorner p.2)) with hv
  set s : Finset (TriangleIndex × Fin 3) :=
    (Finset.univ : Finset (TriangleIndex × Fin 3)).filter fun r =>
      T r.1 r.2 = u ∧
        TriangularHodgeLayer.inverseSigned
          (T r.1 (TriangularHodgeLayer.nextCorner r.2)) = v with hs
  have hp : p ∈ s := by
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ p, hu.symm, hv.symm⟩
  have hp' : p' ∈ s := by
    rw [hs, Finset.mem_filter]
    refine ⟨Finset.mem_univ p', ?_, ?_⟩
    · rw [hu, h1]
    · rw [hv, h2]
  have hcard : 1 < s.card := Finset.one_lt_card.mpr ⟨p, hp, p', hp', hne⟩
  have hdir : 1 < TriangularHodgeLayer.directedAdjacencyCount T u v := hcard
  have hle := hsimple u v
  rw [TriangularHodgeLayer.adjacencyCount] at hle
  omega

/-! ## The decidable checks on a table -/

/-- The collinearity table derived from the link: for distinct vertices, the
number of common neighbours; zero on the diagonal.  For the incidence graph of a
generalized quadrangle this is collinearity of points and concurrence of
lines. -/
def collinearityCount
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (v v' : Generator × Bool) : ℕ :=
  if v = v' then 0
  else ∑ u, TriangularHodgeLayer.adjacencyCount T u v *
    TriangularHodgeLayer.adjacencyCount T u v'

/-- **The finite checks on a triangle table.**  Every clause is an equation or
an inequality between natural numbers computed from the table, so the whole
predicate is decidable; nothing here is an existence statement or a literature
premise.

The girth clause is stated as the absence of four-cycles and of six-cycles: for
a simple bipartite graph that is girth at least `8`, and a positive table always
has a bipartite link. -/
def TableChecks
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ) :
    Prop :=
  2 ≤ q ∧
  7 ≤ q ∧
  (∀ j k, (T j k).2 = true) ∧
  (∀ u, TriangularHodgeLayer.degree T u = q + 1) ∧
  (∀ u v, TriangularHodgeLayer.adjacencyCount T u v ≤ 1) ∧
  (∀ j, ¬ (T j 0 = T j 1 ∧ T j 1 = T j 2)) ∧
  (∀ v v', v ≠ v' →
    (∑ u, TriangularHodgeLayer.adjacencyCount T u v *
      TriangularHodgeLayer.adjacencyCount T u v') ≤ 1) ∧
  (∀ v v', TriangularHodgeLayer.adjacencyCount T v v' = 0 →
    (∑ a, ∑ b, TriangularHodgeLayer.adjacencyCount T v a *
      TriangularHodgeLayer.adjacencyCount T a b *
      TriangularHodgeLayer.adjacencyCount T b v') ≤ 1) ∧
  Fintype.card Generator = (q + 1) * (q ^ 2 + 1) ∧
  (∀ v, (∑ u, collinearityCount T u v) = q * (q + 1)) ∧
  (∀ v v', v.2 ≠ v'.2 → collinearityCount T v v' = 0) ∧
  (∀ v, (∑ u, collinearityCount T u v * collinearityCount T u v)
      = q * (q + 1)) ∧
  (∀ v v', v ≠ v' → v.2 = v'.2 →
    (∑ u, collinearityCount T u v * collinearityCount T u v')
      + 2 * collinearityCount T v v' = q + 1)

noncomputable instance instDecidableTableChecks
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ) :
    Decidable (TableChecks T q) := by
  classical
  infer_instance

/-- A checked table is `(q+1)`-regular; extracted so that the certificate
theorems can use it without unfolding the conjunction. -/
theorem TableChecks.regular
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {q : ℕ}
    (h : TableChecks T q) :
    ∀ u, TriangularHodgeLayer.degree T u = q + 1 :=
  h.2.2.2.1

/-- A checked table has a simple link, so by `corner_unique_of_linkSimple` all
its pieces are single letters and it satisfies `C(3)`. -/
theorem TableChecks.simple
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {q : ℕ}
    (h : TableChecks T q) :
    ∀ u v, TriangularHodgeLayer.adjacencyCount T u v ≤ 1 :=
  h.2.2.2.2.1

/-- A checked table has order at least `7`, which is the spectral threshold
`(q-3)² > 8` for the quadrangle. -/
theorem TableChecks.ord_ge_seven
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {q : ℕ}
    (h : TableChecks T q) : 7 ≤ q :=
  h.2.1

/-! ## The three statements this repository does not prove -/

/-- **The spectral bridge.**  A checked table carries the quadrangle link data
of `GGT/KazhdanHypQuadrangle.lean`.

This is the one residual that is pure bookkeeping: every field of
`QuadrangleLinkData` is one clause of `TableChecks` cast from `ℕ` to `ℚ`.
`adj_square` is definitional once the link is simple and regular, since
`adjacencyCount` is then idempotent and `collinearityCount` is defined to be the
off-diagonal two-step count; `adj_sign` and `col_sign` follow from the two
vanishing clauses, because a nonzero entry forces the two arguments onto
prescribed sides; `col_square` is the strongly regular identity, stated over `ℕ`
in the subtraction-free form `sum + 2*col = q+1`. -/
def QuadrangleDataOfChecks : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ),
    TableChecks T q →
      ∃ Q : QuadrangleLinkData (Generator × Bool),
        (∀ u v, (TriangularHodgeLayer.adjacencyCount T u v : ℚ) = Q.adj u v) ∧
          ((q : ℚ) + 1 = Q.deg)

/-- **Hyperbolicity, by non-metric small cancellation.**  A checked table
satisfies `C(3)` --- pieces are single letters, by `corner_unique_of_linkSimple`
--- and `T(8)` --- the link has girth `8`, by the four-cycle and six-cycle
clauses --- and `1/3 + 1/8 < 1/2`, so the group is hyperbolic.

Not proved here.  What is missing is a van Kampen diagram theory for the
non-metric conditions: this repository's `Sofic/Greendlinger*` development is
`C'(λ)`-metric throughout, and no length-three presentation is `C'(λ)` for any
`λ ≤ 1/3`. -/
def CThreeTEightHyperbolicity : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ),
    TableChecks T q →
      Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T)

/-- **Infiniteness.**  A `C(3)`-`T(8)` group on more than one generator is
infinite, indeed non-elementary; Greendlinger's lemma for the non-metric
conditions gives it.  Not proved here, for the same reason. -/
def CThreeTEightInfinite : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ),
    TableChecks T q → Infinite (TriangularHodgeLayer.Presented T)

/-- **Torsion-freeness, as a hypothesis on the table and not a consequence of
it.**

The module docstring explains why this cannot be folded into `TableChecks`:
Kangaslampi and Vdovina exhibit `23` torsion-free and `168` torsion groups whose
tables all have the same simple link, and a simple link already excludes the
proper-power criterion, so no condition on the link alone separates them.  The
predicate is therefore stated on the table with an unspecified extra
condition `extra`, which is exactly the criterion their classification uses. -/
def TableTorsionFree
    (extra : ∀ (Generator TriangleIndex : Type), [Fintype Generator] →
      [DecidableEq Generator] → [Fintype TriangleIndex] →
      [DecidableEq TriangleIndex] →
      (TriangleIndex → TriangularHodgeLayer.Triangle Generator) → Prop) :
    Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ),
    TableChecks T q → extra Generator TriangleIndex T →
      IsPowerTorsionFree (TriangularHodgeLayer.Presented T)

/-! ## The assembly -/

/-- **A table that passes the checks presents a Kazhdan group.**  The only
input beyond the checks is the spectral bridge, which is bookkeeping; the
Garland certificate and the two completed squares do the rest. -/
theorem hasKazhdanPropertyT_of_tableChecks
    (hbridge : QuadrangleDataOfChecks)
    {Generator TriangleIndex : Type} [fg : Fintype Generator]
    [dg : DecidableEq Generator] [ng : Nonempty Generator]
    [ft : Fintype TriangleIndex] [dt : DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ)
    (h : TableChecks T q) :
    HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented T) := by
  obtain ⟨Q, hadj, hdeg⟩ := hbridge Generator TriangleIndex fg dg ng ft dt T q h
  refine QuadrangleLinkData.hasKazhdanPropertyT_of_quadrangleLink T Q (q + 1)
    (h.regular) ?_ hadj
  rw [← hdeg]
  push_cast
  ring

/-- **`SharpExistence` from a table that passes the checks.**

The hypotheses are the four named statements above and one table.  Property
`(T)` and finite presentation are discharged by the machine; hyperbolicity,
infiniteness and torsion-freeness are the named residuals, and the spectral
bridge is bookkeeping.  A computational lane that exhibits a table passing
`TableChecks` at `q = 8` --- `585` generators, `1755` triangles --- supplies the
only thing that is not a theorem. -/
theorem sharpExistence_of_tableChecks
    {extra : ∀ (Generator TriangleIndex : Type), [Fintype Generator] →
      [DecidableEq Generator] → [Fintype TriangleIndex] →
      [DecidableEq TriangleIndex] →
      (TriangleIndex → TriangularHodgeLayer.Triangle Generator) → Prop}
    (hbridge : QuadrangleDataOfChecks)
    (hhyp : CThreeTEightHyperbolicity)
    (hinf : CThreeTEightInfinite)
    (htf : TableTorsionFree extra)
    {Generator TriangleIndex : Type} [fg : Fintype Generator]
    [dg : DecidableEq Generator] [ng : Nonempty Generator]
    [ft : Fintype TriangleIndex] [dt : DecidableEq TriangleIndex]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (q : ℕ)
    (h : TableChecks T q) (hextra : extra Generator TriangleIndex T) :
    Hyperbolic.SharpExistence :=
  ⟨TriangularHodgeLayer.Presented T, inferInstance,
    hinf Generator TriangleIndex fg dg ng ft dt T q h, inferInstance,
    htf Generator TriangleIndex fg dg ng ft dt T q h hextra,
    hhyp Generator TriangleIndex fg dg ng ft dt T q h,
    hasKazhdanPropertyT_of_tableChecks hbridge T q h⟩

/-! ## The arithmetic of the target table -/

/-- The target table: `q = 8`, `585` generators, link `9`-regular. -/
theorem targetGeneratorCount : (8 + 1) * (8 ^ 2 + 1) = 585 := by norm_num

/-- `3 F = n d` gives `1755` triangles. -/
theorem targetTriangleCount : 585 * 9 = 3 * 1755 := by norm_num

/-- The strictly hyperbolic small-cancellation band, in the `C(3)`-`T(8)` form:
`1/3 + 1/8 < 1/2`, the same inequality as `gromovLinkCondition 3 8`. -/
theorem cThreeTEight_in_band : (1 : ℚ) / 3 + 1 / 8 < 1 / 2 := by norm_num

/-- The Euclidean boundary case `C(3)`-`T(6)`, which is where the `A~_2` tables
sit and where hyperbolicity fails. -/
theorem cThreeTSix_on_boundary : (1 : ℚ) / 3 + 1 / 6 = 1 / 2 := by norm_num

/-- **No length-three presentation is `C'(λ)` for `λ ≤ 1/3`.**  A single-letter
piece has length `1` and a relator has length `3`, so the metric condition
`|piece| < λ |relator|` needs `1 < 3 λ`.  This is why this repository's
`Sofic/Greendlinger*` development, which is metric throughout, cannot be
pointed at a triangle table. -/
theorem lengthThree_not_metric (lam : ℚ) (hlam : lam ≤ 1 / 3) :
    ¬ (1 : ℚ) < 3 * lam := by
  intro h
  linarith

end KazhdanHyp
end GroupApproximation
