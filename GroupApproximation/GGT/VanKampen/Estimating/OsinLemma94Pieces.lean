import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.Estimating.UnboundWordConnectors
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 over two named pieces

Osin (math/0411039v3, §9), Lemma 9.4: "Suppose that `Δ` satisfies `(∗)`.  Let `S`
denote the sum of lengths of all unbound arcs of type (A1) in `Δ`.  Then `S < n √ρ`."
The proof assumes "`S ≥ n √ρ`" and selects a dense component.  Lemma 3.7 on its
polygon gives subsegments `q_1`, `q_2` with `ε`-close endpoints (39), which the two
cases refute: "Case 1 … This contradicts the maximality of `M`."  "Case 2 … This
contradicts our assumption that `∑ l(t_i)` is minimal."

This file names the two halves of that proof and derives `OsinLemma94SectionStatement`
from them.

* `OsinLemma94AntiparallelMetricStatement`, the metric half.  Every dense family of
  closed quasi-geodesic word polygons with at most `K n` sides has a connector pair
  whose target indices run backwards.
* `OsinLemma94PlanarRunInput`, the diagram half.  Every globally distinguished family
  has component polygons (`OsinLemma94PlanarPolygons`) that carry the unbound darts and
  admit no such pair.
* `osinLemma94Section_of_pieces`: the two pieces give `OsinLemma94SectionStatement`.

## Why the pair runs backwards

A `WordConnectorPair` reads the source side forwards, `a < a'`, and leaves the target
indices `b`, `b'` in either order.  Its boundary word is
`source[a, a'] · endConnector · target[b, b']⁻¹ · startConnector`: one connector runs from
`a'` to `b'`, the other from `b` to `a`.  If both sides are read along one face walk,
the four endpoints lie on one circle in the order `a`, `a'`, then `b'`, `b` or `b`, `b'`.
The chords `{a, b}` and `{a', b'}` are disjoint exactly when `b'` comes first, that is
`b' < b`.  Both surgeries of the proof draw the connectors as chords inside the
component: Case 1 fills the quadrilateral by a `G`-disc, Case 2 shortens a cutting path
through a connector.  For `b < b'` the chords cross and there is no such surgery.

The landed metric chain does not fix the orientation.  `SidePair` says "Orientation on
either side is immaterial", and the sampling proof of Lemma 25 ends with
`β ≤ |s' - s|`.  So `OsinLemma94RunInput.no_connector`, which forbids every connector
pair, asks for more than Cases 1 and 2 prove.  Osin's Lemma 3.7 bounds
`max{dist((q_1)_-, (q_2)_-), dist((q_1)_+, (q_2)_+)}` with no orientation either, while
his Case 1 boundary `q_1 s_1 q_2⁻¹ s_2` reads the pair backwards.  Here the metric half
supplies the orientation `C.b' < C.b`, and the diagram half refutes only that case.

## The side budget

Osin counts "`∑ n_i ≤ 53 n`" arcs (Lemma 9.3) and "`k_i ≤ 4 n_i`" sides (38).  The
metric half uses only the total number of sides.  So one constant `K` with
`∑ k_i ≤ K n` replaces both.  The metric half has one threshold for `ε` that serves every
`K`, and only its threshold for `ρ` depends on `K`.  So a diagram half may choose `K` after
`ε`, as the short sides along selected regions need: their number can grow with `ε |M|`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **Dense word polygons carry a backwards connector pair.**

Take `d` closed word polygons at parameters `ε`, `ρ` and side constant `K`.  They have
`∑_k sideCount k ≤ K n` sides, and side `i` of polygon `k` runs from `v k i` to
`v k (i + 1)` along `word k i`.  The sides in `A k` (Osin's class `N1`) and in `B k`
(`N1 ∪ N2`) are `(λ, c)`-quasi-geodesic.  Every other side (class `N3`) has length at
most `ε`.  The `A`-sides have total length at least `n √ρ`.  Then some polygon has a
connector pair from an `A`-side to a different `B`-side whose target indices run
backwards, `b' < b`. -/
def OsinLemma94DensePolygonsAntiparallel {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps rho K : ℕ) : Prop :=
  ∀ (n d : ℕ), 0 < n →
    ∀ (sideCount : Fin d → ℕ) (v : Fin d → ℕ → G)
      (word : Fin d → ℕ → List (RelLetter G Lambda)) (A B : Fin d → Set ℕ),
      (∑ k : Fin d, sideCount k) ≤ K * n →
      (∀ k, v k (sideCount k) = v k 0) →
      (∀ k i, i < sideCount k → v k (i + 1) = v k i * RelLetter.listVal (word k i)) →
      (∀ k i, i < sideCount k → i ∈ A k ∨ i ∈ B k →
        IsLambdaCQuasiGeodesicWord D lambda c (word k i)) →
      (∀ k i, i < sideCount k → i ∉ B k →
        HullSC.RelWord.IsAdmissible D (word k i) ∧ (word k i).length ≤ eps) →
      (n : ℝ) * Real.sqrt (rho : ℝ) ≤
        ∑ k : Fin d, classWordLength (word k) (sideCount k) (A k) →
      ∃ k : Fin d, ∃ C : WordConnectorPair D (v k) (word k) (sideCount k) (A k) (B k) eps,
        C.b' < C.b

/-- **The metric half of Lemma 9.4, oriented.**  For a four-point hyperbolic
`Γ(G, A)`, dense word polygons carry a backwards connector pair at every `ε` above one
threshold, every side constant `K`, and every `ρ` above a threshold chosen after `ε` and `K`.

This is the oriented form of `UnboundEstimate.unboundComponentWordPolygonsMonotone`,
which proves the same conclusion with `b`, `b'` in either order and the constants
`53`, `4` of Lemmas 9.3 and (38).  The thresholds are monotone so that they combine with
the other lemmas of the induction by maxima.  The parameter `μ` and the bound `λ ≤ 1`
play no part in the metric half. -/
def OsinLemma94AntiparallelMetricStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c : ℝ, 0 < lambda → 0 ≤ c →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps → ∀ K : ℕ,
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          OsinLemma94DensePolygonsAntiparallel D lambda c eps rho K

/-- **The component polygons of Lemma 9.4, as the planar surgeries see them.**

For a globally distinguished family `S` (Osin's `M`) there are `count` components cut
open into word polygons.  Side `i` of polygon `k` runs from `corner k i` to
`corner k (i + 1)` along `word k i`.  `relatorSides k` is the class `N1` and
`longSides k` is `N1 ∪ N2`.  Every other side is a class-`N3` side of length at most `ε`.

* `side_budget`: Lemma 9.3 and (38) together, `∑ k_i ≤ K n`.
* `covers`: `S ≤ ∑ S_i`.  Every unbound dart of an `R`-cell lies on an (A1) side.
* `no_antiparallel`: Cases 1 and 2.  No connector pair from an `N1` side to an
  `N1 ∪ N2` side has its target indices running backwards. -/
structure OsinLemma94PlanarPolygons {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps K : ℕ)
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) where
  /-- The number `d` of components `Δ_1, …, Δ_d`. -/
  count : ℕ
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
  /-- Lemma 9.3 and (38): `∑ k_i ≤ K n`. -/
  side_budget : ∑ k, sideCount k ≤ K * Delta.rCellCount
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
  /-- Cases 1 and 2: a backwards pair (39) contradicts the maximality of `M` or the
  minimality of `∑ l(t_j)`. -/
  no_antiparallel : ∀ k (C : WordConnectorPair D (corner k) (word k) (sideCount k)
    (relatorSides k) (longSides k) eps), C.b' < C.b → False

/-- **The diagram half of Lemma 9.4.**  Under the hypotheses of
`OsinLemma94SectionStatement`, there is a side constant `K` and monotone thresholds such
that every globally distinguished family has planar component polygons.

This is the part of the proof that reads the diagram: Lemma 9.3's arc count, the
cutting of (38), and Cases 1 and 2 at the backwards orientation.  The Euler count
`|M| ≤ 3(n + r − 1)` is a binder, as in the statement.  It is weaker than
`OsinLemma94RunInput`, whose producer must also refute forwards pairs. -/
def OsinLemma94PlanarRunInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ K : ℕ, ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) →
                  Nonempty (OsinLemma94PlanarPolygons D lambda c eps K S)

namespace OsinLemma94PlanarPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps K : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **Model test: the fields are consistent.**  With no unbound darts, the empty family
of components carries every field. -/
def ofNoUnbound (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hempty : ∀ i, RegionCandidate.unboundDarts S.family i = ∅) :
    OsinLemma94PlanarPolygons D lambda c eps K S where
  count := 0
  sideCount := Fin.elim0
  corner := Fin.elim0
  word := Fin.elim0
  relatorSides := Fin.elim0
  longSides := Fin.elim0
  side_budget := by simp
  closed := fun k => k.elim0
  step := fun k => k.elim0
  quasiGeodesic := fun k => k.elim0
  short := fun k => k.elim0
  covers := by simp [hempty]
  no_antiparallel := fun k => k.elim0

/-- **The contradiction at fixed parameters.**  "Assume that `S ≥ n √ρ`."  Then the
polygons are dense, the metric half gives a backwards connector pair, and
`no_antiparallel` refutes it. -/
theorem unbound_lt (P : OsinLemma94PlanarPolygons D lambda c eps K S) {rho : ℕ}
    (hcells : 0 < Delta.rCellCount)
    (hmetric : OsinLemma94DensePolygonsAntiparallel D lambda c eps rho K) :
    (∑ i : Fin S.diagram.rCellCount,
        ((RegionCandidate.unboundDarts S.family i).card : ℝ)) <
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) := by
  by_contra hge
  have hdense := le_trans (not_lt.mp hge) P.covers
  obtain ⟨k, pair, hback⟩ := hmetric Delta.rCellCount P.count hcells P.sideCount P.corner
    P.word P.relatorSides P.longSides P.side_budget P.closed P.step P.quasiGeodesic P.short
    hdense
  exact P.no_antiparallel k pair hback

end OsinLemma94PlanarPolygons

/-- **Osin's Lemma 9.4 from its two pieces.**  The diagram half fixes the side constant
`K`.  The thresholds are the maxima of the two halves', the metric threshold for `ρ` is
taken at `K`, and it is positive. -/
theorem osinLemma94Section_of_pieces
    (hmetric : OsinLemma94AntiparallelMetricStatement.{u, w})
    (hrun : OsinLemma94PlanarRunInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨K, eps2, hproducer⟩ := hrun D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, hmetricE⟩ := hmetric D hhyper lambda c hlambda hc
  refine ⟨max eps1 eps2, fun eps heps => ?_⟩
  obtain ⟨rho1, hrho1, hmetricEps⟩ := hmetricE eps (le_trans (le_max_left _ _) heps) K
  obtain ⟨rho2, _, hproducerEps⟩ := hproducer eps (le_trans (le_max_right _ _) heps)
  refine ⟨max rho1 rho2, lt_of_lt_of_le hrho1 (le_max_left _ _), fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hcells S hcard
  obtain ⟨P⟩ := hproducerEps rho (le_trans (le_max_right _ _) hrho) W hW Delta cuts
    hleast hcells S hcard
  exact P.unbound_lt hcells (hmetricEps rho (le_trans (le_max_left _ _) hrho))

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94PlanarPolygons.unbound_lt
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94Section_of_pieces

end GroupApproximation.GGT.VanKampen
