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

end Embedded
end VanKampen
end GGT
end GroupApproximation
