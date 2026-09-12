import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.Estimating.UnboundWordConnectors

/-!
# Osin's Lemma 9.4: the component polygons

Osin (math/0411039v3, §9) proves Lemma 9.4, "`S < n √ρ`", in three layers.

1. **Lemma 9.3, counting.**  Cutting the `R`-cells and the subdiagrams of `M`
   out of `Δ` leaves components `Δ_1, …, Δ_d`.  The boundary of `Δ_i` consists of
   `n_i` arcs of three types: (A1) unbound arcs of `R`-faces, (A2) unbound arcs of
   `∂Δ`, (A3) side arcs of `Γ ∈ M`.  "`#A1 + #A2 ≤ 2|M| + n + r`" and
   "`#A3 ≤ 2|M|`".  The first bound is the statement that every maximal unbound
   run on an `R`-cell, or on a section of `∂Δ`, lies between two region ends
   (or is a whole cell, or a whole section).
2. **(38), cutting.**  `Δ_i` is cut along `l ≤ n_i` paths `t_1, …, t_l` with
   `∑ l(t_j)` minimal, giving a polygon with `k_i ≤ 4 n_i` sides.  "`N2` consist
   of images of segments `t_i^{±1}` … and images of `p̄` for (sub)arcs `p` of type
   (A2).  Further let `N1` and `N3` consist of images of `p̄` for (sub)arcs `p` of
   type (A1) and (A3), respectively."
3. **Lemma 3.7 and the two cases.**  A dense polygon has subsegments `q_1` of
   `p̄_1 ∈ N1` and `q_2` of `p̄_2 ∈ N1 ∪ N2` with `ε`-close endpoints (39).
   "Case 1 … This contradicts the maximality of `M`."  "Case 2 … This contradicts
   our assumption that `∑ l(t_i)` is minimal."

The metric half of layer 3 is `UnboundEstimate.unboundComponentWordPolygonsMonotone`,
which is proved.  This file names the rest as `OsinLemma94RunInput`: every globally
distinguished family has component polygons with Lemma 9.3's arc budget, (38)'s
side bound, the classes `N1`, `N1 ∪ N2`, `N3`, and no connector pair.
`Estimating/OsinLemma94Counting.lean` derives `OsinLemma94SectionStatement` from it.

## Why there is no per-run length bound

Osin bounds no single run.  His threshold is a density per component,
`S_i ≥ n_i √ρ / 60`.  A single run can be as long as a chain of `k_i` short sides
beside it allows, and `k_i ≤ 4 n_i` grows with `n`.  A run bound independent of `n`
is not what the source proves.  A run bound that depends on `n` only gives
`S ≤ (#runs) · bound`, which is quadratic in `n`.  The runs enter the proof through
their number, and `arc_budget` records that number.

## Model tests

* `OsinLemma94ComponentPolygons.ofNoUnbound`: the fields are jointly satisfiable.
  With no unbound darts, the empty family of components carries all of them.
* `osinLemma94_arcBudget_boundary`: at `n = 1`, `r = 4` and `|M| = 3(n + r − 1) = 12`
  the budget `4|M| + n + r` is `53 n` exactly, so the constant `53` of Lemma 9.3 is
  pinned at the boundary.
* `OsinLemma94ComponentPolygons.unbound_lt` (in the counting file): the fields imply
  the conclusion of Lemma 9.4 at the metric scale, so the structure is not weaker
  than what it stands for.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **The complementary components of Lemma 9.4, cut open into word polygons.**

For a globally distinguished family `S` (Osin's `M`) there are `count` components.
Component `k` has `arcCount k` arcs of types (A1)–(A3) (Osin's `n_i`) and, after the
cutting of (38), `sideCount k` sides (Osin's `k_i`).  Side `i` of polygon `k` runs
from `corner k i` to `corner k (i + 1)` along `word k i`.  `relatorSides k` is the
class `N1` and `longSides k` is `N1 ∪ N2`.  Every other side is a class-`N3` side, of
length at most `ε`.

* `arc_budget`: Lemma 9.3, `#A1 + #A2 + #A3 ≤ (2|M| + n + r) + 2|M|`.
* `side_le`: (38), `k_i ≤ 4 n_i`.
* `covers`: `S = ∑ S_i`, as an inequality.  Every unbound dart of an `R`-cell lies on
  an (A1) side.
* `no_connector`: the conclusion of Cases 1 and 2.  No `N1` side and `N1 ∪ N2` side
  carry a pair of long subsegments with `ε`-close geodesic connectors. -/
structure OsinLemma94ComponentPolygons {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) where
  /-- The number `d` of components `Δ_1, …, Δ_d`. -/
  count : ℕ
  /-- `n_i`: the arcs of types (A1)–(A3) on `∂Δ_i`. -/
  arcCount : Fin count → ℕ
  /-- `k_i`: the sides of `Δ_i` cut open along `t_1, …, t_l`. -/
  sideCount : Fin count → ℕ
  /-- The corners of the polygons. -/
  corner : Fin count → ℕ → G
  /-- The side words. -/
  word : Fin count → ℕ → List (RelLetter G Lambda)
  /-- The class `N1`: sides from arcs of type (A1). -/
  relatorSides : Fin count → Set ℕ
  /-- The classes `N1 ∪ N2`: (A1) arcs, cutting paths and (A2) arcs. -/
  longSides : Fin count → Set ℕ
  /-- Lemma 9.3: `#A1 + #A2 ≤ 2|M| + n + r` and `#A3 ≤ 2|M|`. -/
  arc_budget : ∑ k, arcCount k ≤ 4 * S.family.card + Delta.rCellCount + cuts.count
  /-- (38): `k_i ≤ 4 n_i`. -/
  side_le : ∀ k, sideCount k ≤ 4 * arcCount k
  closed : ∀ k, corner k (sideCount k) = corner k 0
  step : ∀ k i, i < sideCount k →
    corner k (i + 1) = corner k i * RelLetter.listVal (word k i)
  /-- (A1) arcs, (A2) arcs and cutting paths are `(λ, c)`-quasi-geodesic. -/
  quasiGeodesic : ∀ k i, i < sideCount k → i ∈ relatorSides k ∨ i ∈ longSides k →
    IsLambdaCQuasiGeodesicWord D lambda c (word k i)
  /-- (A3) arcs: `σ3 ≤ ε k_i`, side by side. -/
  short : ∀ k i, i < sideCount k → i ∉ longSides k →
    HullSC.RelWord.IsAdmissible D (word k i) ∧ (word k i).length ≤ eps
  /-- `S ≤ ∑ S_i`: the unbound darts of the `R`-cells lie on (A1) sides. -/
  covers : (∑ i : Fin S.diagram.rCellCount,
      ((RegionCandidate.unboundDarts S.family i).card : ℝ)) ≤
    ∑ k, classWordLength (word k) (sideCount k) (relatorSides k)
  /-- Cases 1 and 2: an `ε`-close pair (39) contradicts the maximality of `M` or the
  minimality of `∑ l(t_j)`. -/
  no_connector : ∀ k, WordConnectorPair D (corner k) (word k) (sideCount k)
    (relatorSides k) (longSides k) eps → False

/-- **The run input of Osin's Lemma 9.4.**  Under the hypotheses of
`OsinLemma94SectionStatement`, with the same monotone thresholds, every globally
distinguished family has component polygons.

This is the part of the proof that reads the diagram: Lemma 9.3's arc count (every
maximal unbound run lies between two region ends, so `#A1 + #A2 ≤ 2|M| + n + r`),
the cutting of (38), and Cases 1 and 2.  The metric part, Lemma 3.7 on the polygons,
is `UnboundEstimate.unboundComponentWordPolygonsMonotone`.  The Euler count
`|M| ≤ 3(n + r − 1)` is a binder, as in the statement; the producer may ignore it. -/
def OsinLemma94RunInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) →
                  Nonempty (OsinLemma94ComponentPolygons D lambda c eps S)

namespace OsinLemma94ComponentPolygons

/-- **Model test: the fields are consistent.**  With no unbound darts, the empty
family of components carries every field. -/
def ofNoUnbound {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hempty : ∀ i, RegionCandidate.unboundDarts S.family i = ∅) :
    OsinLemma94ComponentPolygons D lambda c eps S where
  count := 0
  arcCount := Fin.elim0
  sideCount := Fin.elim0
  corner := Fin.elim0
  word := Fin.elim0
  relatorSides := Fin.elim0
  longSides := Fin.elim0
  arc_budget := by simp
  side_le := fun k => k.elim0
  closed := fun k => k.elim0
  step := fun k => k.elim0
  quasiGeodesic := fun k => k.elim0
  short := fun k => k.elim0
  covers := by simp [hempty]
  no_connector := fun k => k.elim0

end OsinLemma94ComponentPolygons

/-- **Model test: `53` is pinned.**  At one relator cell, four sections and the
largest family the Euler count `|M| ≤ 3(n + r − 1)` allows, the budget `4|M| + n + r`
equals `53 n`. -/
theorem osinLemma94_arcBudget_boundary : 4 * (3 * (1 + 4 - 1)) + 1 + 4 = 53 * 1 := by
  norm_num

end GroupApproximation.GGT.VanKampen
