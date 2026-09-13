import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94Pieces
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the diagram half over named pieces

Osin (math/0411039v3, §9), Lemma 9.4: "Let `S` denote the sum of lengths of all unbound arcs
of type (A1) in `Δ`.  Then `S < n √ρ`."  `OsinLemma94Pieces.lean` splits the proof into the
metric half, `OsinLemma94AntiparallelMetricStatement`, and the diagram half.  This file splits
the diagram half again, over the faces of the optimal diagram itself.

* `OsinLemma94RealizedPolygons S`: the unselected `G`-faces of `S.diagram`, each face walk cut
  into sides of four kinds.  A side of kind `cell j` is an arc of the `j`-th relator cell (type
  (A1)), `boundary j` an arc of section `j` of `∂Δ` (type (A2)), `cutting` a path with the same
  face on both sides (Osin's cutting paths `t_1, …, t_l`), and `short` a path along a selected
  region (type (A3)).  The side words are the dart labels.  The labels of an optimal family
  are legal over `symmetricLabelAlphabet D` only, so the sides are measured over that
  alphabet, which has the same Cayley graph.  The cutting paths are quasi-geodesic with the
  constant `c + 2`: a subpath that is not can be respelled by a strictly shorter word.
* `OsinLemma94RealizedPolygons.Maximal`: no two consecutive sides of one kind can be joined.
* `GloballyDistinguishedSectionFamily.DartMinimal`: the fewest darts among the optimal families
  with the same unbound sum.  It is the measure for Case 2, in place of `∑ l(t_i)`.

The pieces:

* `OsinLemma94PolygonRealizationInput`: a dart-minimal optimum has maximal polygons.
* `OsinLemma94PolygonCountInput`: `∑ k_i ≤ K n` with `K` chosen before `ε`, and `S ≤ ∑ S_i`
  up to a slack `L n` with `L` chosen after `ε`.
* `OsinLemma94CaseOneInput`: a backwards connector pair whose target is not a cutting side.
* `OsinLemma94CaseTwoInput`: a backwards connector pair whose target is a cutting side.

`osinLemma94Section_of_planarPieces` derives `OsinLemma94SectionStatement` from the metric half
and the four pieces.  The slack costs a factor `2` in `√ρ`: for `ρ ≥ 4 L²` and `ρ ≥ 4 ρ₀` the
metric half is applied at `⌊ρ / 4⌋`.  Every optimal family has the same number of regions, so
passing to a dart-minimal one keeps the Euler count `|M| ≤ 3(n + r − 1)`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **The four kinds of polygon sides** in Lemma 9.4.  `cell j`: an arc of the `j`-th relator
cell, type (A1).  `boundary j`: an arc of section `j` of `∂Δ`, type (A2).  `cutting`: a cutting
path `t_i`.  `short`: a side along a selected region, type (A3). -/
inductive OsinLemma94SideClass (n : ℕ) where
  | cell (j : Fin n)
  | boundary (j : ℕ)
  | cutting
  | short

/-- **The component polygons of Lemma 9.4, on the faces of the optimal diagram.**

Osin cuts each component `Δ_i` "along `t_1, …, t_l`" into a polygon with `k_i` sides.  Here a
component is an unselected `G`-face of `S.diagram`: an inner face that is no relator cell and
lies in no selected region.  The cutting paths are paths of the diagram with this face on both
sides.  The walk of `face k`, rotated by `base k`, is the concatenation of the sides
`sideDarts k 0, …, sideDarts k (sideCount k - 1)`, and `kind k i` says what lies across
side `i`. -/
structure OsinLemma94RealizedPolygons {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) where
  /-- The number of polygons. -/
  count : ℕ
  /-- The face of polygon `k`. -/
  face : Fin count → S.diagram.toCombMap.Face
  face_injective : Function.Injective face
  face_ne_outer : ∀ k, face k ≠ S.diagram.outerFace
  face_not_cell : ∀ k (j : Fin S.diagram.rCellCount), (Embedded.cell S.diagram j).face ≠ face k
  face_unselected : ∀ k, ∀ a ∈ S.family, face k ∉ a.1
  /-- Every unselected `G`-face is the face of a polygon. -/
  face_complete : ∀ f : S.diagram.toCombMap.Face, f ≠ S.diagram.outerFace →
    (∀ j : Fin S.diagram.rCellCount, (Embedded.cell S.diagram j).face ≠ f) →
      (∀ a ∈ S.family, f ∉ a.1) → ∃ k, face k = f
  /-- `k_i`, the number of sides. -/
  sideCount : Fin count → ℕ
  /-- The darts of side `i` of polygon `k`. -/
  sideDarts : Fin count → ℕ → List S.diagram.toCombMap.Dart
  /-- The position on the face walk where side `0` starts. -/
  base : Fin count → ℕ
  walk : ∀ k, (S.diagram.faceBoundary (face k)).darts.rotate (base k) =
    (List.range (sideCount k)).flatMap (sideDarts k)
  side_ne_nil : ∀ k i, i < sideCount k → sideDarts k i ≠ []
  /-- What lies across side `i` of polygon `k`. -/
  kind : Fin count → ℕ → OsinLemma94SideClass S.diagram.rCellCount
  /-- Type (A1): the side is an arc of the `j`-th relator cell, read from across. -/
  cell_arc : ∀ k i (j : Fin S.diagram.rCellCount), i < sideCount k → kind k i = .cell j →
    ∃ arc : Embedded.CyclicArc (Embedded.cellDarts S.diagram j), sideDarts k i = arc.reverseDarts
  /-- Type (A2): the side is an arc of `∂Δ` inside section `j`. -/
  boundary_arc : ∀ k i (j : ℕ), i < sideCount k → kind k i = .boundary j →
    ∃ hj : j < cuts.count, ∃ arc : Embedded.CyclicArc (Embedded.targetDarts S.diagram none),
      sideDarts k i = arc.darts ∧ cuts.cut ⟨j, by omega⟩ ≤ arc.start.1 ∧
        arc.start.1 + arc.length ≤ cuts.cut ⟨j + 1, by omega⟩
  /-- A cutting path: the face across every dart is the face itself. -/
  cutting_internal : ∀ k i, i < sideCount k → kind k i = .cutting →
    ∀ d ∈ sideDarts k i, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = face k
  /-- The walk across a cutting path runs along it, through vertices of degree two. -/
  cutting_interior : ∀ k i, i < sideCount k → kind k i = .cutting →
    ∀ (j : ℕ) (e e' : S.diagram.toCombMap.Dart),
      (sideDarts k i)[j]? = some e → (sideDarts k i)[j + 1]? = some e' →
        S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha e') =
          S.diagram.toCombMap.alpha e
  /-- Type (A3): the side runs along the faces of one selected region. -/
  short_region : ∀ k i, i < sideCount k → kind k i = .short →
    ∃ a ∈ S.family, ∀ d ∈ sideDarts k i,
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1
  /-- The polygon closes up in `G`. -/
  closed : ∀ k, RelLetter.listVal
    ((List.range (sideCount k)).flatMap fun i => Embedded.dartWord S.diagram (sideDarts k i)) = 1
  /-- (A1) arcs, (A2) arcs and cutting paths are `(λ, c + 2)`-quasi-geodesic over the
  symmetric label alphabet. -/
  quasiGeodesic : ∀ k i, i < sideCount k → kind k i ≠ .short →
    IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2)
      (Embedded.dartWord S.diagram (sideDarts k i))
  /-- (A3) sides have length at most `ε`. -/
  short : ∀ k i, i < sideCount k → kind k i = .short →
    HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D)
        (Embedded.dartWord S.diagram (sideDarts k i)) ∧
      (Embedded.dartWord S.diagram (sideDarts k i)).length ≤ eps

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- `S` of Lemma 9.4: the number of unbound darts of the relator cells. -/
noncomputable def unboundSum (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ℕ :=
  ∑ i : Fin S.diagram.rCellCount, (RegionCandidate.unboundDarts S.family i).card

theorem unboundSum_cast (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ((S.unboundSum : ℕ) : ℝ) =
      ∑ i : Fin S.diagram.rCellCount, ((RegionCandidate.unboundDarts S.family i).card : ℝ) := by
  rw [unboundSum, Nat.cast_sum]

/-- **The Case 2 measure.**  "This contradicts our assumption that `∑ l(t_i)` is minimal."
Osin minimizes the total length of the cutting paths.  Here the cutting paths are paths of the
diagram, and the measure is the number of darts, over the optimal families with the same
unbound sum. -/
def DartMinimal (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) : Prop :=
  ∀ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
    T.unboundSum = S.unboundSum → S.diagram.toCombMap.dartCount ≤ T.diagram.toCombMap.dartCount

/-- Two optimal families have the same weight and so the same number of regions. -/
theorem family_card_eq (S T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    S.family.card = T.family.card := by
  have hw : S.toRealizedSectionFamily.weight = T.toRealizedSectionFamily.weight :=
    le_antisymm (T.weight_maximal S.toRealizedSectionFamily S.label_admissible)
      (S.weight_maximal T.toRealizedSectionFamily T.label_admissible)
  exact le_antisymm (S.card_minimal T.toRealizedSectionFamily T.label_admissible hw.symm)
    (T.card_minimal S.toRealizedSectionFamily S.label_admissible hw)

/-- **A dart-minimal optimum exists** with the same number of regions and unbound sum. -/
theorem exists_dartMinimal (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      T.family.card = S.family.card ∧ T.unboundSum = S.unboundSum ∧ T.DartMinimal := by
  classical
  have hex : ∃ m : ℕ, ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      T.unboundSum = S.unboundSum ∧ T.diagram.toCombMap.dartCount = m :=
    ⟨_, S, rfl, rfl⟩
  obtain ⟨T, hTsum, hTm⟩ := Nat.find_spec hex
  refine ⟨T, family_card_eq T S, hTsum, fun T' hT' => ?_⟩
  rw [hTm]
  exact Nat.find_min' hex ⟨T', hT'.trans hTsum, rfl⟩

end GloballyDistinguishedSectionFamily

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The word of side `i` of polygon `k`: the labels of its darts. -/
def word (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ) :
    List (RelLetter G Lambda) :=
  Embedded.dartWord S.diagram (P.sideDarts k i)

/-- The corner of polygon `k` before side `i`. -/
def corner (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ) : G :=
  RelLetter.listVal ((List.range i).flatMap (P.word k))

/-- The class `N1`: sides of type (A1). -/
def relatorSides (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) : Set ℕ :=
  {i | ∃ j, P.kind k i = .cell j}

/-- The classes `N1 ∪ N2`: all sides but those of type (A3). -/
def longSides (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) : Set ℕ :=
  {i | P.kind k i ≠ .short}

/-- **Maximal sides.**  Two consecutive sides of one kind cannot be joined into one side.  For
`cell`, `boundary` and `cutting` sides the walk across turns away at the common vertex.  Two
(A3) sides are together longer than `ε`, or run along no common selected region. -/
def Maximal (P : OsinLemma94RealizedPolygons S) : Prop :=
  ∀ k i, i + 1 < P.sideCount k → P.kind k i = P.kind k (i + 1) →
    ∀ e ∈ (P.sideDarts k i).getLast?, ∀ e' ∈ (P.sideDarts k (i + 1)).head?,
      (P.kind k i ≠ .short →
        S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha e') ≠
          S.diagram.toCombMap.alpha e) ∧
      (P.kind k i = .short →
        eps < (P.sideDarts k i).length + (P.sideDarts k (i + 1)).length ∨
          ¬ ∃ a ∈ S.family, ∀ d ∈ P.sideDarts k i ++ P.sideDarts k (i + 1),
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1)

/-- Lemma 9.3, "`∑ n_i ≤ 53 n`", and (38), "`k_i ≤ 4 n_i`", as one side constant. -/
def SideBudget (P : OsinLemma94RealizedPolygons S) (K : ℕ) : Prop :=
  ∑ k, P.sideCount k ≤ K * Delta.rCellCount

/-- `S ≤ ∑ S_i`, up to `L n`: the unbound darts are covered by the (A1) sides, except for at
most `L n` of them. -/
def Covers (P : OsinLemma94RealizedPolygons S) (L : ℕ) : Prop :=
  (∑ i : Fin S.diagram.rCellCount, ((RegionCandidate.unboundDarts S.family i).card : ℝ)) ≤
    ∑ k, classWordLength (P.word k) (P.sideCount k) (P.relatorSides k) +
      (L : ℝ) * Delta.rCellCount

/-- **Model test: the fields are consistent.**  A diagram with no unselected `G`-face has the
empty family of polygons. -/
def ofNoFaces (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hnone : ∀ f : S.diagram.toCombMap.Face, f ≠ S.diagram.outerFace →
      (∀ j : Fin S.diagram.rCellCount, (Embedded.cell S.diagram j).face ≠ f) →
        (∀ a ∈ S.family, f ∉ a.1) → False) :
    OsinLemma94RealizedPolygons S where
  count := 0
  face := Fin.elim0
  face_injective := by
    intro k
    exact k.elim0
  face_ne_outer := fun k => k.elim0
  face_not_cell := fun k => k.elim0
  face_unselected := fun k => k.elim0
  face_complete := fun f h₁ h₂ h₃ => (hnone f h₁ h₂ h₃).elim
  sideCount := Fin.elim0
  sideDarts := Fin.elim0
  base := Fin.elim0
  walk := fun k => k.elim0
  side_ne_nil := fun k => k.elim0
  kind := Fin.elim0
  cell_arc := fun k => k.elim0
  boundary_arc := fun k => k.elim0
  cutting_internal := fun k => k.elim0
  cutting_interior := fun k => k.elim0
  short_region := fun k => k.elim0
  closed := fun k => k.elim0
  quasiGeodesic := fun k => k.elim0
  short := fun k => k.elim0

/-- The empty family of polygons is maximal. -/
theorem ofNoFaces_maximal (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hnone : ∀ f : S.diagram.toCombMap.Face, f ≠ S.diagram.outerFace →
      (∀ j : Fin S.diagram.rCellCount, (Embedded.cell S.diagram j).face ≠ f) →
        (∀ a ∈ S.family, f ∉ a.1) → False) :
    (ofNoFaces S hnone).Maximal := by
  intro k
  exact k.elim0

theorem corner_step (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ) :
    P.corner k (i + 1) = P.corner k i * RelLetter.listVal (P.word k i) := by
  unfold corner
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
    HullSC.RelWord.listVal_append]

theorem corner_closed (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    P.corner k (P.sideCount k) = P.corner k 0 := by
  unfold corner
  rw [List.range_zero, List.flatMap_nil, RelLetter.listVal_nil]
  exact P.closed k

theorem quasiGeodesic_of_mem (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ)
    (hi : i < P.sideCount k) (hmem : i ∈ P.relatorSides k ∨ i ∈ P.longSides k) :
    IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2) (P.word k i) := by
  refine P.quasiGeodesic k i hi ?_
  rcases hmem with hcell | hlong
  · obtain ⟨j, hj⟩ : ∃ j, P.kind k i = .cell j := hcell
    rw [hj]
    intro h
    cases h
  · exact hlong

theorem short_of_not_mem (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ)
    (hi : i < P.sideCount k) (hnot : i ∉ P.longSides k) :
    HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (P.word k i) ∧
      (P.word k i).length ≤ eps := by
  refine P.short k i hi ?_
  by_contra hne
  exact hnot hne

/-- **The slack costs a factor `2`.**  If `n √ρ ≤ S ≤ ∑ S_i + L n` and `ρ ≥ 4 L²`, then the
polygons are dense at `⌊ρ / 4⌋`. -/
theorem dense_of_covers (P : OsinLemma94RealizedPolygons S) {L rho : ℕ} (hcovers : P.Covers L)
    (hL : 4 * L * L ≤ rho)
    (hge : (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) ≤
      ∑ i : Fin S.diagram.rCellCount, ((RegionCandidate.unboundDarts S.family i).card : ℝ)) :
    (Delta.rCellCount : ℝ) * Real.sqrt ((rho / 4 : ℕ) : ℝ) ≤
      ∑ k, classWordLength (P.word k) (P.sideCount k) (P.relatorSides k) := by
  have hrho : (4 : ℝ) * L * L ≤ rho := by exact_mod_cast hL
  have hquarter : (4 : ℝ) * ((rho / 4 : ℕ) : ℝ) ≤ rho := by
    have h4 : 4 * (rho / 4) ≤ rho := by omega
    exact_mod_cast h4
  have hL0 : (0 : ℝ) ≤ 2 * (L : ℝ) := by positivity
  have hrho0 : (0 : ℝ) ≤ (rho : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ ((rho / 4 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ 2 * Real.sqrt ((rho / 4 : ℕ) : ℝ) := by positivity
  have hn0 : (0 : ℝ) ≤ (Delta.rCellCount : ℝ) := Nat.cast_nonneg _
  have hsqrtL : 2 * (L : ℝ) ≤ Real.sqrt (rho : ℝ) := by
    rw [Real.le_sqrt hL0 hrho0]
    nlinarith
  have hsqrtQ : 2 * Real.sqrt ((rho / 4 : ℕ) : ℝ) ≤ Real.sqrt (rho : ℝ) := by
    rw [Real.le_sqrt hQ0 hrho0, mul_pow, Real.sq_sqrt hm0]
    nlinarith
  have hstep : Real.sqrt ((rho / 4 : ℕ) : ℝ) ≤ Real.sqrt (rho : ℝ) - L := by linarith
  have hn := mul_le_mul_of_nonneg_left hstep hn0
  rw [mul_sub] at hn
  unfold Covers at hcovers
  linarith

/-- **The contradiction at fixed parameters.**  "Assume that `S ≥ n √ρ`."  The polygons are
dense at `⌊ρ / 4⌋`, the metric half gives a backwards connector pair, and the cases refute
it. -/
theorem unbound_lt_of_pieces (P : OsinLemma94RealizedPolygons S) {K L rho rhom : ℕ}
    (hcells : 0 < Delta.rCellCount) (hbudget : P.SideBudget K) (hcovers : P.Covers L)
    (hrhom : 4 * rhom ≤ rho) (hL : 4 * L * L ≤ rho)
    (hmetric : ∀ rho' : ℕ, rhom ≤ rho' →
      OsinLemma94DensePolygonsAntiparallel (symmetricLabelAlphabet D) lambda (c + 2) eps rho' K)
    (hcases : ∀ (k : Fin P.count) (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k)
      (P.word k) (P.sideCount k) (P.relatorSides k) (P.longSides k) eps), C.b' < C.b → False) :
    (∑ i : Fin S.diagram.rCellCount,
        ((RegionCandidate.unboundDarts S.family i).card : ℝ)) <
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) := by
  by_contra hge
  have hdense := P.dense_of_covers hcovers hL (not_lt.mp hge)
  obtain ⟨k, C, hback⟩ := hmetric (rho / 4) (by omega) Delta.rCellCount P.count hcells
    P.sideCount P.corner P.word P.relatorSides P.longSides hbudget P.corner_closed
    (fun k i _ => P.corner_step k i) P.quasiGeodesic_of_mem P.short_of_not_mem hdense
  exact hcases k C hback

end OsinLemma94RealizedPolygons

/-- **Realization piece of Lemma 9.4.**  Under the hypotheses of `OsinLemma94SectionStatement`,
an optimal family with the fewest darts has maximal component polygons.

Osin cuts each component "along `t_1, …, t_l`".  Here the cutting paths are paths of the
diagram and the side words are dart labels.  So the producer makes the cutting paths
quasi-geodesic, cuts (A3) sides into pieces of length at most `ε`, and cuts (A2) arcs at the
section ends. -/
def OsinLemma94PolygonRealizationInput : Prop :=
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
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∃ P : OsinLemma94RealizedPolygons S, P.Maximal

/-- **Count piece of Lemma 9.4.**  Lemma 9.3, "`∑ n_i ≤ 53 n`", and (38), "`k_i ≤ 4 n_i`",
as one side constant `K` chosen before `ε`.  With it, `S ≤ ∑ S_i` up to a slack `L n`, where
`L` is chosen after `ε`.  The slack leaves room for unbound darts on no (A1) side, such as
those along the sides of selected regions, which are at most `ε` long. -/
def OsinLemma94PolygonCountInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ K : ℕ, ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ L : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    P.SideBudget K ∧ P.Covers L

/-- **Case 1 of Lemma 9.4.**  "Case 1 … This contradicts the maximality of `M`."  A backwards
connector pair (39) from an (A1) side to an (A1) or (A2) side of a maximal polygon bounds a new
contiguity region. -/
def OsinLemma94CaseOneInput : Prop :=
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
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ (k : Fin P.count) (C : WordConnectorPair (symmetricLabelAlphabet D)
                      (P.corner k) (P.word k) (P.sideCount k) (P.relatorSides k)
                      (P.longSides k) eps),
                      C.b' < C.b → P.kind k C.target ≠ .cutting → False

/-- **Case 2 of Lemma 9.4.**  "Case 2 … This contradicts our assumption that `∑ l(t_i)` is
minimal."  A backwards connector pair (39) from an (A1) side to a cutting side shortens the
cutting path, against `DartMinimal`. -/
def OsinLemma94CaseTwoInput : Prop :=
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
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ (k : Fin P.count) (C : WordConnectorPair (symmetricLabelAlphabet D)
                      (P.corner k) (P.word k) (P.sideCount k) (P.relatorSides k)
                      (P.longSides k) eps),
                      C.b' < C.b → P.kind k C.target = .cutting → False

/-- **Osin's Lemma 9.4 from the metric half and four planar pieces.**  The count piece fixes
`K`.  The thresholds are the maxima of the pieces', with `ρ₀ ≥ 4 L²` and `ρ₀ ≥ 4 ρ_metric`.
The given family is replaced by a dart-minimal one with the same number of regions and the
same unbound sum. -/
theorem osinLemma94Section_of_planarPieces
    (hmetric : OsinLemma94AntiparallelMetricStatement.{u, w})
    (hreal : OsinLemma94PolygonRealizationInput.{u, w, v})
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hone : OsinLemma94CaseOneInput.{u, w, v})
    (htwo : OsinLemma94CaseTwoInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨K, eps1, hcountK⟩ := hcount D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  have hhyperE : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic (symmetricLabelAlphabet D).alphabet.carrier delta := by
    rw [symmetricLabelAlphabet.carrier_eq]
    exact hhyper
  obtain ⟨eps2, hmetricK⟩ :=
    hmetric (symmetricLabelAlphabet D) hhyperE lambda (c + 2) hlambda (by linarith) K
  obtain ⟨eps3, hrealEps⟩ := hreal D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps4, honeEps⟩ := hone D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps5, htwoEps⟩ := htwo D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps1 (max eps2 (max eps3 (max eps4 eps5))), fun eps heps => ?_⟩
  simp only [max_le_iff] at heps
  obtain ⟨he1, he2, he3, he4, he5⟩ := heps
  obtain ⟨L, rho1, hrho1, hcountEps⟩ := hcountK eps he1
  obtain ⟨rho2, _, hmetricEps⟩ := hmetricK eps he2
  obtain ⟨rho3, _, hrealRho⟩ := hrealEps eps he3
  obtain ⟨rho4, _, honeRho⟩ := honeEps eps he4
  obtain ⟨rho5, _, htwoRho⟩ := htwoEps eps he5
  refine ⟨max rho1 (max (4 * rho2) (max (4 * L * L) (max rho3 (max rho4 rho5)))),
    lt_of_lt_of_le hrho1 (le_max_left _ _), fun rho hrho => ?_⟩
  simp only [max_le_iff] at hrho
  obtain ⟨hr1, hr2, hrL, hr3, hr4, hr5⟩ := hrho
  intro W hW Delta cuts hleast hcells S hcard
  obtain ⟨T, hTcard, hTsum, hTmin⟩ := S.exists_dartMinimal
  have hTcard' : T.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) := by
    rw [hTcard]
    exact hcard
  obtain ⟨P, hP⟩ := hrealRho rho hr3 W hW Delta cuts hleast hcells T hTcard' hTmin
  obtain ⟨hbudget, hcovers⟩ :=
    hcountEps rho hr1 W hW Delta cuts hleast hcells T hTcard' hTmin P hP
  rw [← GloballyDistinguishedSectionFamily.unboundSum_cast S, ← hTsum,
    GloballyDistinguishedSectionFamily.unboundSum_cast T]
  refine P.unbound_lt_of_pieces hcells hbudget hcovers hr2 hrL hmetricEps ?_
  intro k C hback
  by_cases hcut : P.kind k C.target = .cutting
  · exact htwoRho rho hr5 W hW Delta cuts hleast hcells T hTcard' hTmin P hP k C hback hcut
  · exact honeRho rho hr4 W hW Delta cuts hleast hcells T hTcard' hTmin P hP k C hback hcut

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.family_card_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_dartMinimal
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.unbound_lt_of_pieces
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94Section_of_planarPieces

end GroupApproximation.GGT.VanKampen
