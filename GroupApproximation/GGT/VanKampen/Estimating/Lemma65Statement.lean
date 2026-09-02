import GroupApproximation.GGT.VanKampen.Estimating.PhiRealization
import GroupApproximation.GGT.VanKampen.Estimating.PieceCore

/-!
# Osin's Lemma 65, stated verbatim

Lemma `65` of arXiv math/0411039 has two clauses, proved together by induction
on the number of `R`-cells, and this module states them.  Nothing here is
proved; the point is that the induction has ONE conclusion, the conjunction, so
neither clause becomes a standalone residue.

Clause (a) is condition `(*)`: `Phi_M` is simple and every `2`-gon of `Phi'_M`
contains a vertex.  Its multiple-edge half is `Embedded.PhiSimple`, its loop
half is free here (`Embedded.interiorEdge_source_ne_target`, from
`Contiguity.target_ne_source`), and its `2`-gon half is
`Embedded.ExteriorMergeAvailable`.

Clause (b) verbatim: "There is an `R`-cell `Pi` of `Delta` and disjoint
`e`-contiguity subdiagrams `Gamma_j` of `Pi` to sections `q_j`,
`j = 1, ..., r`, of `partial Delta` (some of them may be absent) such that
`sum_{j=1}^r (Pi, Gamma_j, q_j) > 1 - 13 mu`."

## What clause (b) needs that `Embedded.Contiguity` does not have

* **Sections.**  Osin writes `partial Delta = q_1 ... q_r` for `1 <= r <= 4`
  with each `q_j` quasi-geodesic.  The record has no notion of sections; the
  diagram exposes one boundary word.  `BoundarySections` is the missing piece:
  an exact concatenation of `outerDarts`, not a covering.
* **Contiguity degree.**  `(Pi, Gamma, q) = l(q_1) / l(partial Pi)`.  The
  algebraic side already has this, twice, as `CellContiguity.degree` and
  `BoundaryContiguity.degree`, both `(arc length) / (source word length)`;
  `Contiguity.degree` is the embedded mirror.
* **Targeting a section**, rather than the whole boundary: `TargetsSection`.
* **"Some of them may be absent"**: carried by summing over a `Finset` of
  present indices rather than over all of `Fin r`.

## What it already has

`target_ne_source` and `o52Certificate` are exactly the `O52` input the
induction consumes, and `pasting` gives the boundary value identity.  Disjoint
subdiagrams are `Embedded.Compatible`, which is disjointness of the carriers.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC
open scoped BigOperators

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {D : GGT.RelGenSet G Lambda}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-! ## The missing vocabulary -/

/-- **The embedded contiguity degree**, `(Pi, Gamma, q) = l(q_1)/l(partial Pi)`.
Mirrors `CellContiguity.degree` and `BoundaryContiguity.degree` on the
algebraic side, which are both `(arc length) / (source word length)`. -/
noncomputable def Contiguity.degree
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) : ℝ :=
  (Gamma.sourceArc.length : ℝ) / ((cell Delta Gamma.source).word.length : ℝ)

/-- **Osin's `partial Delta = q_1 ... q_r`**, `1 <= r <= 4`, each section
`(lambda, c)`-quasi-geodesic.  The decomposition is an exact concatenation of
the oriented outer darts, matching the source rather than merely covering
them. -/
structure BoundarySections
    (D : GGT.RelGenSet G Lambda) (lambda c : ℝ)
    (Delta : DiscDiagram.{u, w, v} W) where
  /-- The number `r` of sections. -/
  count : ℕ
  count_pos : 0 < count
  count_le : count ≤ 4
  /-- The `j`-th section, as a dart list. -/
  part : Fin count → List Delta.toCombMap.Dart
  /-- `partial Delta = q_1 ... q_r`. -/
  decomposition : outerDarts Delta = (List.ofFn part).flatten
  /-- Each section is `(lambda, c)`-quasi-geodesic. -/
  quasiGeodesic : ∀ j,
    IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta (part j))

/-- A region is a contiguity of its source cell **to the section** `q`: its
target is the outer boundary and its target arc lies inside `q`. -/
def Contiguity.TargetsSection
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (q : List Delta.toCombMap.Dart) : Prop :=
  Gamma.target = none ∧ ∀ d ∈ Gamma.targetArc.darts, d ∈ q

/-- **Osin's `2 mu`, embedded, with no equations hypothesis.**  In the
multiple-edge step Osin writes "(Pi, Gamma_2, t_1) + (Pi, Gamma_4, t_2) < 2 mu
by Lemma O52".  Here the region supplies its own `CellPieceEquations` from its
`pasting` and `o52Certificate` fields, so the estimate needs only reducedness
and the small-cancellation data.  This is the input to step (2) of the joint
induction. -/
theorem Contiguity.degree_le_two_mu
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (hred : Delta.Reduced)
    {target : Fin Delta.rCellCount} (htarget : Gamma.target = some target)
    {rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length)
    (hlen : 0 < ((cell Delta Gamma.source).word.length : ℝ)) :
    Gamma.degree ≤ 2 * mu := by
  have equations := Gamma.cellPieceEquations_of_reduced hred htarget
  have hbound := Gamma.arcLengths_le_two_mu_source equations hsc hpieces
  have hnn : (0 : ℝ) ≤
      ((Gamma.cellTargetArc equations.target equations.target_eq).length : ℝ) :=
    Nat.cast_nonneg _
  rw [Contiguity.degree, div_le_iff₀ hlen]
  linarith

/-! ## The two clauses -/

/-- **Clause (b), verbatim.**  One `R`-cell `Pi`, disjoint contiguity
subdiagrams of `Pi` to the sections, some possibly absent, with total degree
above `1 - 13 mu`. -/
def Lemma65bConclusion (mu : ℝ) {lambda c : ℝ}
    (sections : BoundarySections D lambda c Delta) (eps : ℕ) : Prop :=
  ∃ (source : Fin Delta.rCellCount)
    (present : Finset (Fin sections.count))
    (faces : Fin sections.count → Finset Delta.toCombMap.Face)
    (Gamma : ∀ j, Contiguity D eps Delta (faces j)),
    (∀ j ∈ present, (Gamma j).source = source) ∧
      (∀ j ∈ present, (Gamma j).TargetsSection (sections.part j)) ∧
      (∀ j ∈ present, ∀ k ∈ present, j ≠ k → Disjoint (faces j) (faces k)) ∧
      1 - 13 * mu < ∑ j ∈ present, (Gamma j).degree

/-- **Clause (a)**, in the two halves this formalization still owes.  The loop
half is already a theorem, so it does not appear. -/
def Lemma65aConclusion
    (scaffold : EstimatingScaffold D eps Delta) : Prop :=
  PhiSimple scaffold.selected.family ∧
    ExteriorMergeAvailable scaffold.selected.family

/-- **The conclusion of Lemma 65 at one diagram.**  Osin states both clauses
"up to passing to an `O`-equivalent diagram", and they hold on one and the same
diagram, so the conjunction is asserted at a single scaffold. -/
def Lemma65Conclusion
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ) (lambda c mu : ℝ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) : Prop :=
  ∃ Delta' : DiscDiagram.{u, w, v} W,
    Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
      ∃ (sections' : BoundarySections D lambda c Delta')
        (scaffold : EstimatingScaffold D eps Delta'),
        Lemma65aConclusion scaffold ∧ Lemma65bConclusion mu sections' eps

/-- **Lemma 65, as one statement.**  Both clauses hold after passing to an
`O`-equivalent diagram.  The induction on the `R`-cell count has this
conjunction as its conclusion, which is why neither clause is stated as a
separate residue: the multiple-edge half of (a) is proved from the inductive
instance of (b), and (b) is proved using (a) at the same stage.

The parameters are the ones the source names.  `mu <= 1/16` is spent in
`multipleEdge_contradiction`; `0 < rho` and the `C`-condition give every
`R`-cell a boundary of positive length; and
`lambda⁻¹ (3 eps + c) < (mu / 2) rho` is Osin's "if `rho` is large enough" in
the side-arc estimate, the only other place a parameter inequality is used. -/
def Lemma65Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (lambda c mu : ℝ)
    {W : Set (List (GGT.RelLetter G Lambda))},
    OsinCCondition D W eps mu lambda c rho →
    0 < lambda → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 → 0 < rho →
    lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) →
    ∀ (Delta : DiscDiagram.{u, w, v} W)
      (sections : BoundarySections D lambda c Delta),
      Delta.Reduced → 0 < Delta.rCellCount →
        Lemma65Conclusion D eps lambda c mu Delta

/-- **Osin's `mu`, per region.**  Sharper than `degree_le_two_mu`, and the one
the multiple-edge step needs: Osin writes "(Pi, Gamma_2, t_1) + (Pi, Gamma_4,
t_2) < 2 mu by Lemma O52", which is `mu` for each of the two regions, not `2 mu`
for their sum.  The published-piece bound already bounds the *source arc alone*
by `mu` times the carrier length; the `2 mu` statement bounds the sum of a
single region's two arcs, which is too weak here -- two regions at `2 mu` each
would give `5 mu` against `1 - 13 mu`, and that does not contradict
`mu <= 1/16`. -/
theorem Contiguity.degree_lt_mu
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (hred : Delta.Reduced)
    {target : Fin Delta.rCellCount} (htarget : Gamma.target = some target)
    {rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length)
    (hlen : 0 < ((cell Delta Gamma.source).word.length : ℝ)) :
    Gamma.degree < mu := by
  have equations := Gamma.cellPieceEquations_of_reduced hred htarget
  have hpublished := Gamma.isPublishedPiece_of_equations equations hsc
  have hbound := hpieces
    (dartWord Delta Gamma.sourceArc.darts)
    (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))
    (dartWord Delta Gamma.sourceArc.rotated) hpublished
  have hsource : (Gamma.sourceArc.length : ℝ) <
      mu * (dartWord Delta Gamma.sourceArc.rotated).length := by
    simpa only [dartWord, List.length_map, Gamma.sourceArc.darts_length] using
      lt_of_le_of_lt (le_max_left _ _) hbound
  have hcarrier : (dartWord Delta Gamma.sourceArc.rotated).length =
      (cell Delta Gamma.source).word.length := by
    simp only [dartWord, List.length_map, Gamma.sourceArc.rotated_length]
    have hlength := congrArg List.length
      (dartWord_cellDarts Delta Gamma.source)
    simpa only [dartWord, List.length_map, targetDarts] using hlength
  rw [hcarrier] at hsource
  rw [Contiguity.degree, div_lt_iff₀ hlen]
  linarith

/-! ## The arithmetic of the multiple-edge step -/

/-- **Osin's numeric contradiction, exactly.**  In the multiple-edge step the
inductive instance of clause (b) gives a degree sum above `1 - 13 mu` for the
four arcs `s_1, t_1, s_2, t_2`; Lemma `O52` bounds the two cell-to-cell terms by
`2 mu` and the two side-arc terms by `mu / 2` each, so the sum is below `3 mu`.
"We obtain a contradiction since `1 - 13 mu > 3 mu` for `mu < 1/16`."

This is where `mu <= 1/16` is actually spent, and it is the only place. -/
theorem multipleEdge_contradiction {mu d₁ d₂ d₃ d₄ : ℝ}
    (hmu : mu ≤ 1 / 16)
    (hsum : 1 - 13 * mu < d₁ + d₂ + d₃ + d₄)
    (hinner : d₂ + d₄ ≤ 2 * mu)
    (hside₁ : d₁ < mu / 2) (hside₃ : d₃ < mu / 2) : False := by
  linarith

/-! ## The cut, as data -/

/-- **The subdiagram enclosed by two contiguity regions between the same pair
of cells.**  Osin: "Consider a subdiagram `Xi` in `Delta` such that: (i)
`partial Xi = s_1 t_1 s_2 t_2`, where `s_j` is a side arc of `Theta_j` and
`t_j` is a subpath of `partial Pi_j`; (ii) `Xi` does not contain `Pi_1` and
`Pi_2`."

`rCellCount_lt` is clause (ii), "the number of `R`-cells in `Xi` is smaller
than `n`".  `rCellCount_pos` is *not* surgery: it is Osin's "By the definition
of `M`, we can not include `Theta_1` and `Theta_2` into a single
`e`-contiguity subdiagram ... This means that `Xi` contains at least one
`R`-cell", so it is discharged from the distinguished family, not from the
cut.  `reduced` is inherited, since a subdiagram of a reduced diagram is
reduced. -/
structure Lemma65CutData
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (D : GGT.RelGenSet G Lambda) (lambda c : ℝ)
    (Delta : DiscDiagram.{u, w, v} W) where
  /-- The enclosed subdiagram `Xi`. -/
  enclosed : DiscDiagram.{u, w, v} W
  /-- Osin's clause (ii): fewer `R`-cells, which is what the induction descends
  on. -/
  rCellCount_lt : enclosed.rCellCount < Delta.rCellCount
  /-- From the definition of `M`, not from the surgery. -/
  rCellCount_pos : 0 < enclosed.rCellCount
  /-- Reducedness is inherited. -/
  reduced : enclosed.Reduced
  /-- Osin's clause (i), `partial Xi = s_1 t_1 s_2 t_2`: the four arcs are a
  boundary decomposition of the enclosed subdiagram into quasi-geodesic
  sections, which is what lets the inductive assumption apply to it.  Each
  `s_j` is a side arc of a distinguished region, so it is short and geodesic;
  each `t_j` is a subpath of a relator-cell boundary, so it is
  `(lambda, c)`-quasi-geodesic by the `C`-condition. -/
  sections : BoundarySections D lambda c enclosed

/-- **Existence of the cut.**  Two distinct selected regions with the same
source and the same target cell enclose such a subdiagram.  This is the one
statement the induction needs from the surgery side; the cut is a different
operation from `SurgeryMap.replaceGRegion`, which collapses a face set rather
than cutting along a four-arc closed walk. -/
def Lemma65CutStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W},
    OsinCCondition D W eps mu lambda c rho →
    Delta.Reduced →
    ∀ (selected : Finset (Candidate D eps Delta))
      (e₁ e₂ : InteriorEdge selected),
      e₁ ≠ e₂ →
        e₁.candidate.contiguity.source = e₂.candidate.contiguity.source →
          e₁.target = e₂.target →
            Nonempty (Lemma65CutData D lambda c Delta)

/-! ## The side-arc estimate -/

/-- Every relator cell has a boundary of positive length, since the
`C`-condition makes every word of the family at least `rho` long. -/
theorem cellWord_length_pos
    {rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho) (hrho : 0 < rho)
    (i : Fin Delta.rCellCount) :
    (0 : ℝ) < ((cell Delta i).word.length : ℝ) := by
  have hlong : rho ≤ (cell Delta i).word.length :=
    hsc.long (cell Delta i).word (cell Delta i).word_mem
  have hpos : 0 < (cell Delta i).word.length := lt_of_lt_of_le hrho hlong
  exact_mod_cast hpos

/-- **Osin's side-arc estimate, arithmetic half.**  "if `u` is a contiguity arc
of `Pi` to `s_1`, then `l(u) <= lambda^{-1}(3 e + c)` since `u` is
`(lambda, c)`-quasi-geodesic and `l(s_1) <= e`.  Therefore
`(Pi, Gamma_1, s_1) = l(u)/l(partial Pi) < l(u)/rho < mu/2` if `rho` is large
enough."  The length bound on the source arc is the geometric half and is an
input; everything after it is this computation, with "`rho` is large enough"
spelled out as `lambda⁻¹ (3 eps + c) < (mu / 2) rho`. -/
theorem Contiguity.degree_lt_half_mu_of_sourceArc_le
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    {rho : ℕ} {mu lambda c : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hmu : 0 < mu) (hrho : 0 < rho)
    (hbound : (Gamma.sourceArc.length : ℝ) ≤ lambda⁻¹ * (3 * (eps : ℝ) + c))
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ)) :
    Gamma.degree < mu / 2 := by
  have hlong : rho ≤ (cell Delta Gamma.source).word.length :=
    hsc.long (cell Delta Gamma.source).word (cell Delta Gamma.source).word_mem
  have hlongR : (rho : ℝ) ≤ ((cell Delta Gamma.source).word.length : ℝ) := by
    exact_mod_cast hlong
  have hpos : (0 : ℝ) < ((cell Delta Gamma.source).word.length : ℝ) :=
    cellWord_length_pos hsc hrho Gamma.source
  have hhalf : (0 : ℝ) ≤ mu / 2 := by linarith
  have hmul : mu / 2 * (rho : ℝ) ≤
      mu / 2 * ((cell Delta Gamma.source).word.length : ℝ) :=
    mul_le_mul_of_nonneg_left hlongR hhalf
  rw [Contiguity.degree, div_lt_iff₀ hpos]
  linarith

/-! ## The induction, and what it consumes -/

/-- **The inductive assumption of Lemma 65**: the conclusion at every reduced
diagram with fewer than `n` `R`-cells that carries a boundary decomposition
into at most four quasi-geodesic sections. -/
def Lemma65Below
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ) (lambda c mu : ℝ)
    (W : Set (List (GGT.RelLetter G Lambda))) (n : ℕ) : Prop :=
  ∀ (Xi : DiscDiagram.{u, w, v} W)
    (sections : BoundarySections D lambda c Xi),
    Xi.rCellCount < n → Xi.Reduced → 0 < Xi.rCellCount →
      Lemma65Conclusion D eps lambda c mu Xi

/-- **The obligations of Lemma 65 that are not the cut.**

* `sideArcSourceLength` is the geometric half of the side-arc estimate: a
  contiguity arc of `Pi` to a section of length at most `e` is
  `(lambda, c)`-quasi-geodesic between points at distance at most `3 e`, so it
  is at most `lambda⁻¹ (3 e + c)` long.  The arithmetic half is
  `Contiguity.degree_lt_half_mu_of_sourceArc_le`.
* `ambientTransport` reads the four regions of the inductive instance of clause
  (b) inside the cut as regions of the ambient diagram: `Gamma_2` and
  `Gamma_4` become regions of `Pi` to the cells `Pi_1` and `Pi_2`, which is why
  Lemma `O52` applies to them, and `Gamma_1`, `Gamma_3` target the two side
  arcs, which have length at most `e`.
* `mergeAvailable` is the `2`-gon half of `(*)`: "one can include the
  `e`-contiguity subdiagrams corresponding to the edges `e` and `f` into a
  single `e`-contiguity subdiagram".
* `clauseB` is Osin's part (b): Corollary `64` -- itself Lemma `63`, so Lemma
  `Eul` and Lemma `62` under `(*)` -- together with the minimality argument on
  `m(Pi)`, which consumes the same inductive assumption and so takes it as an
  argument.  At one `R`-cell it is the base case of the induction; the other
  three fields are vacuous there.

The multiple-edge half of `(*)`, the descent through the cut and the numeric
contradiction are proved from these in `lemma65_of_inputs`. -/
structure Lemma65Inputs : Prop where
  /-- The contiguity arc of a cell to a short section is short. -/
  sideArcSourceLength : ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (q : List Delta.toCombMap.Dart),
    OsinCCondition D W eps mu lambda c rho →
    0 < lambda →
    Gamma.TargetsSection q →
    q.length ≤ eps →
      (Gamma.sourceArc.length : ℝ) ≤ lambda⁻¹ * (3 * (eps : ℝ) + c)
  /-- The four regions of the cut, read in the ambient diagram. -/
  ambientTransport : ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {mu lambda c : ℝ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (e₁ e₂ : InteriorEdge selected),
    e₁ ≠ e₂ →
    e₁.candidate.contiguity.source = e₂.candidate.contiguity.source →
    e₁.target = e₂.target →
    ∀ (cut : Lemma65CutData D lambda c Delta)
      (Xi : DiscDiagram.{u, w, v} W),
      Nonempty (OEquivalentDiscDiagram cut.enclosed Xi) →
      ∀ (sections : BoundarySections D lambda c Xi),
        Lemma65bConclusion mu sections eps →
          ∃ (faces₁ faces₂ faces₃ faces₄ : Finset Delta.toCombMap.Face)
            (Gamma₁ : Contiguity D eps Delta faces₁)
            (Gamma₂ : Contiguity D eps Delta faces₂)
            (Gamma₃ : Contiguity D eps Delta faces₃)
            (Gamma₄ : Contiguity D eps Delta faces₄)
            (t₂ t₄ : Fin Delta.rCellCount)
            (q₁ q₃ : List Delta.toCombMap.Dart),
            Gamma₂.target = some t₂ ∧ Gamma₄.target = some t₄ ∧
              Gamma₁.TargetsSection q₁ ∧ Gamma₃.TargetsSection q₃ ∧
              q₁.length ≤ eps ∧ q₃.length ≤ eps ∧
              1 - 13 * mu <
                Gamma₁.degree + Gamma₂.degree + Gamma₃.degree + Gamma₄.degree
  /-- Two distinct outer regions at one cell merge into a single region of at
  least their combined weight. -/
  mergeAvailable : ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (scaffold : EstimatingScaffold D eps Delta),
    Delta.Reduced → ExteriorMergeAvailable scaffold.selected.family
  /-- Clause (b) from clause (a) and the inductive assumption. -/
  clauseB : ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (sections : BoundarySections D lambda c Delta)
    (scaffold : EstimatingScaffold D eps Delta),
    OsinCCondition D W eps mu lambda c rho →
    Delta.Reduced → 0 < Delta.rCellCount →
    Lemma65aConclusion scaffold →
    Lemma65Below D eps lambda c mu W Delta.rCellCount →
      Lemma65Conclusion D eps lambda c mu Delta

/-- **Lemma 65, from the cut and the four obligations.**  The induction is on
the number of `R`-cells.  At each stage the multiple-edge half of `(*)` is
proved by contradiction: two distinct selected regions between the same ordered
pair of cells cut out a subdiagram with fewer `R`-cells and at least one, the
inductive instance of clause (b) applies to it, its four regions transport to
the ambient diagram, Lemma `O52` bounds the two cell-to-cell degrees by `mu`
each and the side-arc estimate bounds the other two by `mu/2` each, and
`1 - 13 mu > 3 mu` for `mu <= 1/16`.  Clause (b) is then Osin's part (b) at the
same stage. -/
theorem lemma65_of_inputs
    (hcut : Lemma65CutStatement.{u, w, v})
    (hin : Lemma65Inputs.{u, w, v}) :
    Lemma65Statement.{u, w, v} := by
  intro G _ Lambda D eps rho lambda c mu W hcondition hlambda hc hmu hmuUpper
    hrho hlarge
  have key : ∀ n : ℕ, ∀ Delta : DiscDiagram.{u, w, v} W,
      Delta.rCellCount ≤ n →
      ∀ _sections : BoundarySections D lambda c Delta,
        Delta.Reduced → 0 < Delta.rCellCount →
          Lemma65Conclusion D eps lambda c mu Delta := by
    intro n
    induction n with
    | zero =>
        intro Delta hle _sections hred hcells
        exact absurd hcells (by omega)
    | succ n ih =>
        intro Delta hle sections hred hcells
        obtain ⟨scaffold⟩ := exists_estimatingScaffold D eps Delta
        have hbelow : Lemma65Below D eps lambda c mu W Delta.rCellCount := by
          intro Xi sectionsXi hlt hredXi hcellsXi
          exact ih Xi (by omega) sectionsXi hredXi hcellsXi
        have hsimple : PhiSimple scaffold.selected.family := by
          intro e₁ e₂ hsource htarget
          by_contra hne
          obtain ⟨cut⟩ : Nonempty (Lemma65CutData D lambda c Delta) :=
            hcut hcondition hred scaffold.selected.family e₁ e₂ hne hsource
              htarget
          obtain ⟨Xi, hOXi, sectionsXi, scaffoldXi, haXi, hbXi⟩ :=
            hbelow cut.enclosed cut.sections cut.rCellCount_lt cut.reduced
              cut.rCellCount_pos
          obtain ⟨faces₁, faces₂, faces₃, faces₄, Gamma₁, Gamma₂, Gamma₃,
            Gamma₄, t₂, t₄, q₁, q₃, htarget₂, htarget₄, hsection₁, hsection₃,
            hshort₁, hshort₃, hsum⟩ :=
            hin.ambientTransport scaffold.selected.family e₁ e₂ hne hsource
              htarget cut Xi hOXi sectionsXi hbXi
          have hd₂ : Gamma₂.degree < mu :=
            Gamma₂.degree_lt_mu hred htarget₂ hcondition.toIsSmallCancellation
              hcondition.publishedPiecesSmall
              (cellWord_length_pos hcondition.toIsSmallCancellation hrho
                Gamma₂.source)
          have hd₄ : Gamma₄.degree < mu :=
            Gamma₄.degree_lt_mu hred htarget₄ hcondition.toIsSmallCancellation
              hcondition.publishedPiecesSmall
              (cellWord_length_pos hcondition.toIsSmallCancellation hrho
                Gamma₄.source)
          have hd₁ : Gamma₁.degree < mu / 2 :=
            Gamma₁.degree_lt_half_mu_of_sourceArc_le
              hcondition.toIsSmallCancellation hmu hrho
              (hin.sideArcSourceLength Gamma₁ q₁ hcondition hlambda hsection₁
                hshort₁)
              hlarge
          have hd₃ : Gamma₃.degree < mu / 2 :=
            Gamma₃.degree_lt_half_mu_of_sourceArc_le
              hcondition.toIsSmallCancellation hmu hrho
              (hin.sideArcSourceLength Gamma₃ q₃ hcondition hlambda hsection₃
                hshort₃)
              hlarge
          have hinner : Gamma₂.degree + Gamma₄.degree ≤ 2 * mu := by linarith
          exact multipleEdge_contradiction hmuUpper hsum hinner hd₁ hd₃
        exact hin.clauseB Delta sections scaffold hcondition hred hcells
          ⟨hsimple, hin.mergeAvailable scaffold hred⟩ hbelow
  intro Delta sections hred hcells
  exact key Delta.rCellCount Delta le_rfl sections hred hcells

/-! ## Model checks -/

/-- Model check at one relator cell: clause (a)'s multiple-edge half is
vacuous, because there are no interior edges at all. -/
theorem phiSimple_of_rCellCount_one
    (hone : Delta.rCellCount = 1)
    (selected : Finset (Candidate D eps Delta)) :
    PhiSimple selected := by
  intro e₁ e₂ _ _
  exfalso
  have hsrc : e₁.candidate.contiguity.source = e₁.target := by
    apply Fin.ext
    have h1 := e₁.candidate.contiguity.source.isLt
    have h2 := e₁.target.isLt
    omega
  exact interiorEdge_source_ne_target e₁ hsrc

/-- Model check: a region targeting a section does target the outer boundary,
so both `O52` fields are vacuous on it.  This is why the sections of clause (b)
cost nothing on the certificate side. -/
theorem target_eq_none_of_targetsSection
    {faces : Finset Delta.toCombMap.Face}
    {Gamma : Contiguity D eps Delta faces}
    {q : List Delta.toCombMap.Dart}
    (h : Gamma.TargetsSection q) : Gamma.target = none :=
  h.1

/-- Model check at one relator cell: there are no interior edges, so the
premises of `Lemma65Inputs.ambientTransport` cannot be met there. -/
theorem interiorEdge_isEmpty_of_rCellCount_one
    (hone : Delta.rCellCount = 1)
    (selected : Finset (Candidate D eps Delta)) :
    IsEmpty (InteriorEdge selected) := by
  constructor
  intro e
  have hsrc : e.candidate.contiguity.source = e.target := by
    apply Fin.ext
    have h1 := e.candidate.contiguity.source.isLt
    have h2 := e.target.isLt
    omega
  exact interiorEdge_source_ne_target e hsrc

/-- Model check at one relator cell: the cut has no room, since its subdiagram
would have to carry at least one `R`-cell and fewer than one. -/
theorem lemma65CutData_isEmpty_of_rCellCount_one
    (D : GGT.RelGenSet G Lambda) (lambda c : ℝ)
    (hone : Delta.rCellCount = 1) :
    IsEmpty (Lemma65CutData D lambda c Delta) := by
  constructor
  intro cut
  have h1 := cut.rCellCount_lt
  have h2 := cut.rCellCount_pos
  omega

/-- Model check at one relator cell: clause (a) costs only the merge input, so
clause (b) is the whole base case of the induction. -/
theorem lemma65aConclusion_of_rCellCount_one
    (hone : Delta.rCellCount = 1)
    (scaffold : EstimatingScaffold D eps Delta)
    (hmerge : ExteriorMergeAvailable scaffold.selected.family) :
    Lemma65aConclusion scaffold :=
  ⟨phiSimple_of_rCellCount_one hone scaffold.selected.family, hmerge⟩

end Embedded
end VanKampen
end GGT
end GroupApproximation
