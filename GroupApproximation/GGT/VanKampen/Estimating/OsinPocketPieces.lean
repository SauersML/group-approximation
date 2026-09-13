import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFollowsBoundary
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellArcs
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionDarts
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixDescentCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixGreendlingerPocketParts
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The pieces of the section pocket cut

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Let `Π` be a cell of the optimal
diagram with two distinct exterior regions to one section `q_j`.  Between them lies a
subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`: the sides `s_1`, `s_2` of the two regions, no
longer than `ε`, an arc `t_1` of `∂Π` and an arc `t_2` of `q_j`.  When `Γ_1` keeps an `R`-cell,
it is least area with fewer cells and four sections, and regions of copies of `Γ_1` to `t_1`
and `t_2` glue back into regions of copies of `Δ`.  This module states the pieces of that
construction and assembles `SectionPocketCutInput` from them.

## The pieces and their owners, in the order of the assembly

* `SectionPocketFaceSetInput` (lane `kh-ejz`; the kept cell through the zero-cell merge of lane
  `hull-select`): the face set between the two regions as a `PocketFaceSet`, with its boundary
  cycle split as `s_1 t_1 s_2 t_2` and a relator cell inside.
* `PocketPinchStatement` (lane `hull-respell`): an O-equivalent copy whose pocket face set is
  simple, its boundary cycle a simple closed walk, by simple circuits or a 0-refinement.
* `PocketRegionOfSimpleStatement` (lane `dgo-analytic`, `Estimating/OsinPocketRegionOfSimple`
  through `PocketRegion.ofSimpleClosedWalk`): a simple pocket face set is a `PocketCarrier`, a
  `PocketRegion` with both cycles following the boundary and the same split of the complement's
  cycle.
* `PocketCollarStatement` (lane `kh-torsion`): an O-equivalent copy with a collared carrier, whose
  sides are geodesic words, by a collar of `G`-faces along each side.
* `PocketCellTransportStatement` and `PocketOuterTransportStatement` (lane `go-lemma42`): regions
  of copies of the pocket to an arc of a cell outside, or to an arc of `∂X`, glue back into
  regions of copies of `X`.

## What is proved here

* `PocketCarrier.nonempty_osinSectionPocketCut`: a collared carrier in an O-equivalent copy of a
  least-area `Δ`, in the positions of section `j`, gives an `OsinSectionPocketCut`, given the
  two transports.  The sides are quasi-geodesic as geodesic words, `t_1` as an arc of a relator
  read backwards, and `t_2` as an infix of section `j`.
* `sectionPocketCutInput_of_pieces` and `osinSectionPocketCutSection_of_pieces`:
  `SectionPocketCutInput`, and its uniform statement, from the pieces.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric
open scoped Classical

section Carriers

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The face set between two exterior regions** (Osin's `Γ_1`).  A face set away from the
exterior face, with a relator cell `kept` inside and the cell `source` outside, whose boundary
cycle is `s_1 t_1 s_2 t_2`: a side `s_1`, an arc `t_1` of `source` read backwards, a side `s_2`,
and an arc `t_2` of `∂X` between the positions `lo` and `hi`.  The sides and their values are no
longer than `ε`. -/
structure PocketFaceSet (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    (lo hi : ℕ) where
  faces : Finset X.toCombMap.Face
  outerFace_not_mem : X.outerFace ∉ faces
  source : Fin X.rCellCount
  source_not_mem : (cell X source).face ∉ faces
  kept : Fin X.rCellCount
  kept_mem : (cell X kept).face ∈ faces
  sourceArc : CyclicArc (cellDarts X source)
  targetArc : CyclicArc (outerDarts X)
  firstSide : List X.toCombMap.Dart
  secondSide : List X.toCombMap.Dart
  boundary : Surgery.MapCollapse.BoundaryCycle X.toCombMap faces
  decomposition : boundary.cycle =
    firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts
  firstSide_length_le : firstSide.length ≤ eps
  secondSide_length_le : secondSide.length ≤ eps
  firstSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps
  secondSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps
  lo_le : lo ≤ targetArc.start.1
  le_hi : targetArc.start.1 + targetArc.length ≤ hi

namespace PocketFaceSet

variable {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A simple pocket**: the boundary cycle is a simple closed walk, with no two darts starting
at the same vertex, so that `PocketRegion.ofSimpleClosedWalk` makes its side a pocket region. -/
def Simple (K : PocketFaceSet D eps X lo hi) : Prop :=
  IsSimpleClosedWalk X.toCombMap K.boundary.cycle

theorem Simple.isSimpleClosedWalk {K : PocketFaceSet D eps X lo hi} (hK : K.Simple) :
    IsSimpleClosedWalk X.toCombMap K.boundary.cycle :=
  hK

end PocketFaceSet

/-- **The pocket carrier.**  A `PocketRegion` of `X` whose cycles follow the boundary, with a
relator cell `kept` inside and the cell `source` outside, and the inverse cycle of the complement
split as `s_1 t_1 s_2 t_2`: sides no longer than `ε`, with values no longer than `ε`, an arc
`t_1` of `source` read backwards, and an arc `t_2` of `∂X` between the positions `lo` and
`hi`. -/
structure PocketCarrier (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    (lo hi : ℕ) where
  pocket : PocketRegion X
  inner_follows : pocket.inner.FollowsBoundary
  outer_follows : pocket.outer.FollowsBoundary
  source : Fin X.rCellCount
  source_not_mem : (cell X source).face ∉ pocket.faces
  kept : Fin X.rCellCount
  kept_mem : (cell X kept).face ∈ pocket.faces
  sourceArc : CyclicArc (cellDarts X source)
  targetArc : CyclicArc (outerDarts X)
  firstSide : List X.toCombMap.Dart
  secondSide : List X.toCombMap.Dart
  decomposition : invDarts X pocket.outer.cycle =
    firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts
  firstSide_length_le : firstSide.length ≤ eps
  secondSide_length_le : secondSide.length ≤ eps
  firstSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps
  secondSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps
  lo_le : lo ≤ targetArc.start.1
  le_hi : targetArc.start.1 + targetArc.length ≤ hi

namespace PocketCarrier

variable {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Collared sides**: both sides are admissible geodesic words, as after a collar of `G`-faces
labelled by geodesic words for the side values. -/
def Collared (K : PocketCarrier D eps X lo hi) : Prop :=
  RelWord.IsAdmissible D (dartWord X K.firstSide) ∧
    RelWord.IsAdmissible D (dartWord X K.secondSide) ∧
    (dartWord X K.firstSide).length =
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X K.firstSide)) ∧
    (dartWord X K.secondSide).length =
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X K.secondSide))

end PocketCarrier

end Carriers

/-! ## The pieces -/

section FaceSetInput

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The face set between two exterior regions** (lane `kh-ejz`; the kept cell through the
zero-cell merge of lane `hull-select`).  Two distinct exterior regions of one cell of a globally
distinguished family to section `j` enclose a `PocketFaceSet` of the optimal diagram in the
positions of section `j`.  A pocket without a relator cell merges the two regions, against the
choice of the family. -/
def SectionPocketFaceSetInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count),
          ∀ a ∈ RegionCandidate.exteriorAt S.family i,
            ∀ b ∈ RegionCandidate.exteriorAt S.family i, a ≠ b →
              RegionCandidate.TargetsSectionIndex cuts j a →
                RegionCandidate.TargetsSectionIndex cuts j b →
                  Nonempty (PocketFaceSet D eps S.diagram (cuts.cut j.castSucc)
                    (cuts.cut j.succ))

end FaceSetInput

/-- **The face set producer, uniformly in the parameters** (lane `kh-ejz`), with the quantifier
prefix of `OsinSectionPocketCutSectionStatement`. -/
def OsinSectionPocketFaceSetSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              SectionPocketFaceSetInput.{u, w, v} D lambda c eps W

/-- **The pinched pocket** (lane `hull-respell`).  A pocket face set has an O-equivalent copy with
a simple pocket face set in the same positions, by simple circuits or a 0-refinement. -/
def PocketPinchStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    PocketFaceSet D eps X lo hi →
      ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
        Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple

/-- **The pocket region of a simple pocket** (lane `dgo-analytic`).  A simple pocket face set is a
pocket carrier: its boundary cycle is a simple closed walk, whose side is a pocket region by
`PocketRegion.ofSimpleClosedWalk`, and the complement's cycle reads `s_1 t_1 s_2 t_2`
backwards. -/
def PocketRegionOfSimpleStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ)
    (K : PocketFaceSet D eps X lo hi), K.Simple →
      Nonempty (PocketCarrier D eps X lo hi)

/-- **The collar** (lane `kh-torsion`, `GGT/VanKampen/SurgeryGeodesicCollar.lean`).  A pocket
carrier has an O-equivalent copy with a collared pocket carrier in the same positions: along each
side a collar of `G`-faces labelled by a geodesic word for the side value, of length at most
`ε`. -/
def PocketCollarStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    PocketCarrier D eps X lo hi →
      ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketCarrier D eps X' lo hi),
        Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Collared

/-- **Transport to a cell** (lane `go-lemma42`).  Let the inverse complement cycle of a pocket
region of `X` contain, after `pre`, an arc of a cell `t` outside the pocket read backwards.  A
region of an O-equivalent copy of the pocket to that part of its boundary glues back into a
region of an O-equivalent copy of `X` from a cell to another cell, with the same contiguity
degree. -/
def PocketCellTransportStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (P : PocketRegion X),
    P.outer.FollowsBoundary →
      ∀ (t : Fin X.rCellCount), (cell X t).face ∉ P.faces →
        ∀ (arc : CyclicArc (cellDarts X t)) (pre post : List X.toCombMap.Dart),
          invDarts X P.outer.cycle = pre ++ invDarts X arc.darts ++ post →
            ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram P.diagram Xi →
              ∀ a : RegionCandidate D eps Xi, a.2.target = none →
                pre.length ≤ a.2.targetArc.start.1 →
                  a.2.targetArc.start.1 + a.2.targetArc.length ≤ pre.length + arc.length →
                    ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
                      (t' : Fin Y.rCellCount),
                      Nonempty (OEquivalentDiscDiagram X Y) ∧ b.2.target = some t' ∧
                        b.2.source ≠ t' ∧ b.contiguityDegree = a.contiguityDegree

/-- **Transport to the boundary** (lane `go-lemma42`).  Let the inverse complement cycle of a
pocket region of `X` contain, after `pre`, an arc of `∂X` without wrap-around.  A region of an
O-equivalent copy of the pocket to that part of its boundary glues back into a region of an
O-equivalent copy of `X` to `∂X` inside the arc, with the same contiguity degree. -/
def PocketOuterTransportStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (P : PocketRegion X),
    P.outer.FollowsBoundary →
      ∀ (arc : CyclicArc (outerDarts X)), arc.start.1 + arc.length ≤ (outerDarts X).length →
        ∀ (pre post : List X.toCombMap.Dart),
          invDarts X P.outer.cycle = pre ++ arc.darts ++ post →
            ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram P.diagram Xi →
              ∀ a : RegionCandidate D eps Xi, a.2.target = none →
                pre.length ≤ a.2.targetArc.start.1 →
                  a.2.targetArc.start.1 + a.2.targetArc.length ≤ pre.length + arc.length →
                    ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y),
                      Nonempty (OEquivalentDiscDiagram X Y) ∧ b.2.target = none ∧
                        arc.start.1 ≤ b.2.targetArc.start.1 ∧
                        b.2.targetArc.start.1 + b.2.targetArc.length ≤
                          arc.start.1 + arc.length ∧
                        b.contiguityDegree = a.contiguityDegree

/-! ## The assembly -/

section Assembly

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

private theorem partsCut_map_map {α β : Type*} (f : α → β) (parts : List (List α)) (k : ℕ) :
    CutSections.partsCut (parts.map (List.map f)) k = CutSections.partsCut parts k := by
  unfold CutSections.partsCut
  rw [← List.map_take, ← List.map_flatten, List.length_map]

private theorem partsCut_four_one {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] 1 = a.length := by
  simp [CutSections.partsCut]

private theorem partsCut_four_two {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] (1 + 1) = a.length + b.length := by
  simp [CutSections.partsCut]

private theorem partsCut_four_three {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] 3 = a.length + b.length + c.length := by
  simp [CutSections.partsCut, Nat.add_assoc]

private theorem partsCut_four_four {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] (3 + 1) =
      a.length + b.length + c.length + d.length := by
  simp [CutSections.partsCut, Nat.add_assoc]

/-- **The section pocket cut from a collared carrier.**  Let `Δ` be least area, `X` an
O-equivalent copy, and `K` a collared pocket carrier of `X` in the positions of section `j`.
Under `C(ε, μ, λ, c, ρ)` with `λ ≤ 1` and `0 ≤ c`, the four parts are quasi-geodesic: the sides
as geodesic words, `t_1` as an arc of a relator read backwards, and `t_2` as an infix of section
`j`.  So the pocket is a least area cut with four sections, and the two transports glue its
regions to `t_1` and `t_2` back. -/
theorem PocketCarrier.nonempty_osinSectionPocketCut
    (hcell : PocketCellTransportStatement.{u, w, v})
    (houter : PocketOuterTransportStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    {Delta X : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (equiv : OEquivalentDiscDiagram Delta X)
    (cuts : SectionCuts D lambda c Delta.boundaryWord) (j : Fin cuts.count)
    (K : PocketCarrier D eps X (cuts.cut j.castSucc) (cuts.cut j.succ)) (hK : K.Collared) :
    Nonempty (OsinSectionPocketCut D lambda c eps Delta cuts j) := by
  have hlength : (outerDarts X).length = Delta.boundaryWord.length := by
    rw [← equiv.boundaryWord_eq, ← dartWord_outerDarts X]
    simp only [dartWord, List.length_map]
  have hend : K.targetArc.start.1 + K.targetArc.length ≤ (outerDarts X).length := by
    have hmono : cuts.cut j.succ ≤ cuts.cut (Fin.last cuts.count) :=
      cuts.cut_mono (Fin.le_last _)
    rw [cuts.cut_last] at hmono
    have hhi := K.le_hi
    omega
  have hdarts : K.targetArc.darts =
      ((outerDarts X).drop K.targetArc.start.1).take K.targetArc.length := by
    have hle : K.targetArc.length ≤ ((outerDarts X).drop K.targetArc.start.1).length := by
      rw [List.length_drop]
      omega
    rw [CyclicArc.darts, CyclicArc.rotated, List.take_append_of_le_length hle]
  have hsection : IsLambdaCQuasiGeodesicWord D lambda c (dartWord X K.targetArc.darts) := by
    have hlo := K.lo_le
    have hhi := K.le_hi
    have hq := CutSections.isLambdaCQuasiGeodesicWord_drop_take (cuts.quasiGeodesic j)
      (K.targetArc.start.1 - cuts.cut j.castSucc) K.targetArc.length
    have heq : (((Delta.boundaryWord.drop (cuts.cut j.castSucc)).take
          (cuts.cut j.succ - cuts.cut j.castSucc)).drop
          (K.targetArc.start.1 - cuts.cut j.castSucc)).take K.targetArc.length =
        (Delta.boundaryWord.drop K.targetArc.start.1).take K.targetArc.length := by
      rw [List.drop_take, List.drop_drop, List.take_take, Nat.add_sub_of_le hlo]
      congr 1
      omega
    rw [heq] at hq
    rw [hdarts, SectionCuts.dartWord_outerDarts_drop_take, equiv.boundaryWord_eq]
    exact hq
  have hslope : ∀ n : ℕ, (lambda - 1) * (n : ℝ) ≤ c := by
    intro n
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hlambda) h0]
  have hquasi : ∀ part ∈ [K.firstSide, invDarts X K.sourceArc.darts, K.secondSide,
      K.targetArc.darts], IsLambdaCQuasiGeodesicWord D lambda c (dartWord X part) := by
    intro part hpart
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
    rcases hpart with rfl | rfl | rfl | rfl
    · exact CutSections.isLambdaCQuasiGeodesicWord_of_geodesic D hK.1 hK.2.2.1 hc (hslope _)
    · exact CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts hcondition K.sourceArc
    · exact CutSections.isLambdaCQuasiGeodesicWord_of_geodesic D hK.2.1 hK.2.2.2 hc (hslope _)
    · exact hsection
  have key := K.pocket.fourSectionCuts_leastAreaCut D lambda c eps (equiv.leastArea hlea)
    (cell_mem X K.kept) K.kept_mem (cell_mem X K.source) K.source_not_mem
    K.firstSide (invDarts X K.sourceArc.darts) K.secondSide K.targetArc.darts K.decomposition
    hquasi K.firstSide_length_le K.secondSide_length_le
  let S := K.pocket.fourSectionCuts D lambda c K.firstSide (invDarts X K.sourceArc.darts)
    K.secondSide K.targetArc.darts K.decomposition hquasi
  have hcut : ∀ k : Fin (S.count + 1), S.cut k = CutSections.partsCut
      [K.firstSide, invDarts X K.sourceArc.darts, K.secondSide, K.targetArc.darts] k :=
    fun k => partsCut_map_map X.label
      [K.firstSide, invDarts X K.sourceArc.darts, K.secondSide, K.targetArc.darts] k
  have hinv : (invDarts X K.sourceArc.darts).length = K.sourceArc.length := by
    rw [invDarts, List.length_map, List.length_reverse, CyclicArc.darts_length]
  have htarget : K.targetArc.darts.length = K.targetArc.length := CyclicArc.darts_length _
  have hcellT : ∀ k : Fin S.count, (k : ℕ) = 1 →
      ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram K.pocket.diagram Xi →
        ∀ a : RegionCandidate D eps Xi, RegionCandidate.TargetsSectionIndex S k a →
          ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y) (t : Fin Y.rCellCount),
            Nonempty (OEquivalentDiscDiagram Delta Y) ∧ b.2.target = some t ∧
              b.2.source ≠ t ∧ b.contiguityDegree = a.contiguityDegree := by
    intro k hk Xi E a ha
    obtain ⟨hnone, hlo, hhi⟩ := ha
    rw [hcut, Fin.val_castSucc, hk, partsCut_four_one] at hlo
    rw [hcut, Fin.val_succ, hk, partsCut_four_two, hinv] at hhi
    obtain ⟨Y, b, t, ⟨EY⟩, hbt, hne, hdeg⟩ := hcell D eps W X K.pocket K.outer_follows K.source
      K.source_not_mem K.sourceArc K.firstSide (K.secondSide ++ K.targetArc.darts)
      (by simp only [K.decomposition, List.append_assoc]) Xi E a hnone hlo hhi
    exact ⟨Y, b, t, ⟨equiv.trans EY⟩, hbt, hne, hdeg⟩
  have hsecT : ∀ k : Fin S.count, (k : ℕ) = 3 →
      ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram K.pocket.diagram Xi →
        ∀ a : RegionCandidate D eps Xi, RegionCandidate.TargetsSectionIndex S k a →
          ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y),
            Nonempty (OEquivalentDiscDiagram Delta Y) ∧
              RegionCandidate.TargetsSectionIndex cuts j b ∧
              b.contiguityDegree = a.contiguityDegree := by
    intro k hk Xi E a ha
    obtain ⟨hnone, hlo, hhi⟩ := ha
    rw [hcut, Fin.val_castSucc, hk, partsCut_four_three] at hlo
    rw [hcut, Fin.val_succ, hk, partsCut_four_four, htarget] at hhi
    obtain ⟨Y, b, ⟨EY⟩, hbnone, hblo, hbhi, hdeg⟩ := houter D eps W X K.pocket K.outer_follows
      K.targetArc hend (K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide) []
      (by simp only [K.decomposition, List.append_nil]) Xi E a hnone
      (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
    exact ⟨Y, b, ⟨equiv.trans EY⟩,
      (show b.2.target = none ∧ cuts.cut j.castSucc ≤ b.2.targetArc.start.1 ∧
          b.2.targetArc.start.1 + b.2.targetArc.length ≤ cuts.cut j.succ from
        ⟨hbnone, K.lo_le.trans hblo, hbhi.trans K.le_hi⟩), hdeg⟩
  exact ⟨{ enclosed := K.pocket.diagram
           leastArea := key.1
           rCellCount_pos := key.2.1
           rCellCount_lt := lt_of_lt_of_eq key.2.2.1 equiv.rCellCount_eq
           sections := S
           count_eq := key.2.2.2.1
           side_short := key.2.2.2.2
           cellTransport := hcellT
           sectionTransport := hsecT }⟩

/-- **`SectionPocketCutInput` from the pieces.**  The face set between the two regions is made
simple, turned into a carrier, and collared, in successive O-equivalent copies of the optimal
diagram, which is O-equivalent to `Δ`. -/
theorem sectionPocketCutInput_of_pieces
    (hpinch : PocketPinchStatement.{u, w, v})
    (hregion : PocketRegionOfSimpleStatement.{u, w, v})
    (hcollar : PocketCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v})
    (houter : PocketOuterTransportStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hfaces : SectionPocketFaceSetInput.{u, w, v} D lambda c eps W) :
    SectionPocketCutInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨K⟩ := hfaces Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X₁, K₁, ⟨E₁⟩, hsimple⟩ := hpinch D eps W S.diagram _ _ K
  obtain ⟨C⟩ := hregion D eps W X₁ _ _ K₁ hsimple
  obtain ⟨X₂, C₂, ⟨E₂⟩, hC₂⟩ := hcollar D eps W X₁ _ _ C
  exact PocketCarrier.nonempty_osinSectionPocketCut hcell houter hcondition hlambda hc hlea
    ((S.equiv.trans E₁).trans E₂) cuts j C₂ hC₂

end Assembly

/-- **The section pocket producer from the pieces, uniformly in the parameters**, at the
thresholds of the face set producer. -/
theorem osinSectionPocketCutSection_of_pieces
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchStatement.{u, w, v})
    (hregion : PocketRegionOfSimpleStatement.{u, w, v})
    (hcollar : PocketCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v})
    (houter : PocketOuterTransportStatement.{u, w, v}) :
    OsinSectionPocketCutSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hfaces D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition =>
    sectionPocketCutInput_of_pieces hpinch hregion hcollar hcell houter hcondition hlambda1 hc
      (hrho rho hrho' W hcondition)⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.Simple
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.Simple.isSimpleClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketCarrier.Collared
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketFaceSetInput
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketFaceSetSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketPinchStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegionOfSimpleStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketCollarStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketCellTransportStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketOuterTransportStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketCarrier.nonempty_osinSectionPocketCut
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketCutInput_of_pieces
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketCutSection_of_pieces
