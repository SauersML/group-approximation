import GroupApproximation.GGT.HullSCLemma49FromRelativeGreendlinger
import GroupApproximation.GGT.VanKampen.Estimating.PieceBridge

/-!
# Exterior cyclic arcs for Hull's Lemma 4.9

The source form of relative Greendlinger returns an embedded contiguity region
whose source and outer arcs are cyclic arcs in their carrier boundaries.  This
module extracts the exact word data used by Hull's Lemma 4.9.  The source cell
is rotated so its exposed arc is a prefix, and the two connector elements are
replaced by geodesic words of length at most `epsilon`.

When the outer cyclic arc does not cross the selected basepoint, it is turned
into the based `Lemma49RelativeGreendlingerCell` consumed by the existing
correction and prime-piece arguments.  The crossing case is isolated as a
literal rotation of the power boundary, with no loss in the exterior estimate.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w v

end HullSC

namespace GGT.VanKampen.Embedded

/-- An outer-target embedded contiguity has a cyclic target arc on the
oriented outer dart cycle. -/
def Contiguity.outerTargetArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : GGT.VanKampen.DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (htarget : Gamma.target = none) : CyclicArc (outerDarts Delta) := by
  have hcycle : targetDarts Delta Gamma.target = outerDarts Delta := by
    rw [htarget]
    rfl
  exact {
    start := Fin.cast
      (congrArg (fun cycle => cycle.length + 1) hcycle)
        Gamma.targetArc.start
    length := Gamma.targetArc.length
    length_le := by
      rw [← hcycle]
      exact Gamma.targetArc.length_le }

/-- The outer target arc keeps the stored cyclic length. -/
theorem Contiguity.outerTargetArc_length
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : GGT.VanKampen.DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (htarget : Gamma.target = none) :
    (Gamma.outerTargetArc htarget).length = Gamma.targetArc.length := by
  rfl

/-- Mapping the oriented outer dart cycle to labels preserves its length and
produces the disc boundary word. -/
theorem outerDarts_length_eq_boundaryWord_length
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : GGT.VanKampen.DiscDiagram.{u, w, v} W) :
    (outerDarts Delta).length = Delta.boundaryWord.length := by
  have h := congrArg List.length (dartWord_outerDarts Delta)
  simpa only [dartWord, List.length_map] using h

end GGT.VanKampen.Embedded

namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

/-! ## Extracted cyclic word data -/

/-- The source-faithful exterior-cell output in word form.  Both the relator
and boundary carriers are rotated to the starts of the embedded cyclic arcs.
The boundary start is retained so a later lemma can distinguish whether the
arc crosses the chosen basepoint. -/
structure Lemma49EmbeddedExteriorArc
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (v : List (GGT.RelLetter G Lambda))
    (g : G) (n eps : ℕ) (mu : ℝ)
    (Z : Lemma49GeodesicPowerDiagram D v g n) where
  relator : List (GGT.RelLetter G Lambda)
  exterior : List (GGT.RelLetter G Lambda)
  remainder : List (GGT.RelLetter G Lambda)
  relator_decomposition : relator = exterior ++ remainder
  relator_mem : relator ∈ RelWord.symmetrized v
  boundaryStart : ℕ
  boundaryStart_le : boundaryStart ≤
    (lemma49BoundaryPower Z.boundaryWord n).length
  boundaryArc : List (GGT.RelLetter G Lambda)
  boundaryAfter : List (GGT.RelLetter G Lambda)
  boundary_rotation_decomposition :
    (lemma49BoundaryPower Z.boundaryWord n).rotate boundaryStart =
      boundaryArc ++ boundaryAfter
  leftSide : List (GGT.RelLetter G Lambda)
  rightSide : List (GGT.RelLetter G Lambda)
  leftSide_admissible : RelWord.IsAdmissible D leftSide
  rightSide_admissible : RelWord.IsAdmissible D rightSide
  leftSide_short : leftSide.length ≤ eps
  rightSide_short : rightSide.length ≤ eps
  exterior_value : GGT.RelLetter.listVal exterior =
    GGT.RelLetter.listVal leftSide *
      GGT.RelLetter.listVal boundaryArc *
        GGT.RelLetter.listVal rightSide
  exterior_large :
    (1 - 23 * mu) * (relator.length : ℝ) ≤ (exterior.length : ℝ)

/-! ## Extraction from an embedded region -/

/-- A source Gr0 embedded exterior region gives the cyclic word data needed
by Lemma 4.9.  `harcs` is the boundary-value equation of the G-cell face set;
its orientation follows the source-reverse, right, outer, left order in
`Embedded.Contiguity.boundary_decomposition`. -/
theorem exists_lemma49EmbeddedExteriorArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ} {mu : ℝ}
    (Z : Lemma49GeodesicPowerDiagram D v g n)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v) eps mu rho)
    {Delta : GGT.VanKampen.DiscDiagram.{u, w, v} (RelWord.symmetrized v)}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : GGT.VanKampen.Embedded.Contiguity D eps Delta faces)
    (htarget : Gamma.target = none)
    (hboundary : Delta.boundaryWord =
      lemma49BoundaryPower Z.boundaryWord n)
    (hmu : 0 ≤ mu)
    (hlarge :
      (1 - 13 * mu) *
          ((GGT.VanKampen.Embedded.cell Delta Gamma.source).word.length : ℝ) <
        (Gamma.sourceArc.length : ℝ))
    (harcs :
      GGT.RelLetter.listVal
          (GGT.VanKampen.Embedded.dartWord Delta Gamma.sourceArc.darts) =
        GGT.RelLetter.listVal
            (GGT.VanKampen.Embedded.dartWord Delta Gamma.rightSide) *
          GGT.RelLetter.listVal
            (GGT.VanKampen.Embedded.dartWord Delta
              (Gamma.outerTargetArc htarget).darts) *
          GGT.RelLetter.listVal
            (GGT.VanKampen.Embedded.dartWord Delta Gamma.leftSide)) :
    Nonempty (Lemma49EmbeddedExteriorArc D v g n eps mu Z) := by
  let outerArc := Gamma.outerTargetArc htarget
  obtain ⟨sourceRemainder, hsourceSplit⟩ :=
    Gamma.sourceArc.exists_dartWord_suffix
  obtain ⟨boundaryAfter, hboundarySplit⟩ :=
    outerArc.exists_dartWord_suffix
  let leftElement : G := GGT.RelLetter.listVal
    (GGT.VanKampen.Embedded.dartWord Delta Gamma.rightSide)
  let rightElement : G := GGT.RelLetter.listVal
    (GGT.VanKampen.Embedded.dartWord Delta Gamma.leftSide)
  obtain ⟨leftSide, hleftGeo⟩ :=
    GGT.OsinComponents.existsGeodesicWord D 1 leftElement
  obtain ⟨rightSide, hrightGeo⟩ :=
    GGT.OsinComponents.existsGeodesicWord D 1 rightElement
  have hleftValue : GGT.RelLetter.listVal leftSide = leftElement := by
    simpa only [one_mul] using hleftGeo.2.1
  have hrightValue : GGT.RelLetter.listVal rightSide = rightElement := by
    simpa only [one_mul] using hrightGeo.2.1
  have hleftLength : leftSide.length ≤ eps := by
    rw [hleftGeo.2.2, wordDist_one_left]
    exact Gamma.rightSide_norm_le
  have hrightLength : rightSide.length ≤ eps := by
    rw [hrightGeo.2.2, wordDist_one_left]
    exact Gamma.leftSide_norm_le
  have hsourceWord :
      GGT.VanKampen.Embedded.dartWord Delta Gamma.sourceArc.rotated =
        GGT.VanKampen.Embedded.dartWord Delta Gamma.sourceArc.darts ++
          sourceRemainder := hsourceSplit
  have hsourceMem :
      GGT.VanKampen.Embedded.dartWord Delta Gamma.sourceArc.rotated ∈
        RelWord.symmetrized v := by
    exact Gamma.sourceArc.cell_rotated_mem hinput.toIsSmallCancellation
  have hboundaryRotation :
      (lemma49BoundaryPower Z.boundaryWord n).rotate outerArc.start.1 =
        GGT.VanKampen.Embedded.dartWord Delta outerArc.darts ++
          boundaryAfter := by
    calc
      (lemma49BoundaryPower Z.boundaryWord n).rotate outerArc.start.1 =
          Delta.boundaryWord.rotate outerArc.start.1 := by rw [hboundary]
      _ = (GGT.VanKampen.Embedded.dartWord Delta
            (GGT.VanKampen.Embedded.outerDarts Delta)).rotate
              outerArc.start.1 := by
        rw [GGT.VanKampen.Embedded.dartWord_outerDarts]
      _ = GGT.VanKampen.Embedded.dartWord Delta outerArc.rotated := by
        exact (outerArc.dartWord_rotated).symm
      _ = GGT.VanKampen.Embedded.dartWord Delta outerArc.darts ++
          boundaryAfter := hboundarySplit
  have hstart : outerArc.start.1 ≤
      (lemma49BoundaryPower Z.boundaryWord n).length := by
    have hstartOuter : outerArc.start.1 ≤
        (GGT.VanKampen.Embedded.outerDarts Delta).length := by
      omega
    calc
      outerArc.start.1 ≤
          (GGT.VanKampen.Embedded.outerDarts Delta).length := hstartOuter
      _ = Delta.boundaryWord.length :=
        GGT.VanKampen.Embedded.outerDarts_length_eq_boundaryWord_length Delta
      _ = (lemma49BoundaryPower Z.boundaryWord n).length :=
        congrArg List.length hboundary
  have hrelatorLength :
      (GGT.VanKampen.Embedded.dartWord Delta
          Gamma.sourceArc.rotated).length =
        (GGT.VanKampen.Embedded.cell Delta Gamma.source).word.length := by
    simp only [GGT.VanKampen.Embedded.dartWord, List.length_map,
      Gamma.sourceArc.rotated_length]
    have hcell := congrArg List.length
      (GGT.VanKampen.Embedded.dartWord_cellDarts Delta Gamma.source)
    simpa only [GGT.VanKampen.Embedded.dartWord, List.length_map] using hcell
  have hexteriorLength :
      (GGT.VanKampen.Embedded.dartWord Delta
          Gamma.sourceArc.darts).length = Gamma.sourceArc.length := by
    simp only [GGT.VanKampen.Embedded.dartWord, List.length_map,
      Gamma.sourceArc.darts_length]
  have hlargeWeak :
      (1 - 23 * mu) *
          ((GGT.VanKampen.Embedded.dartWord Delta
            Gamma.sourceArc.rotated).length : ℝ) ≤
        (GGT.VanKampen.Embedded.dartWord Delta
          Gamma.sourceArc.darts).length := by
    rw [hrelatorLength, hexteriorLength]
    have hperimeter : (0 : ℝ) ≤
        ((GGT.VanKampen.Embedded.cell Delta Gamma.source).word.length : ℝ) := by
      positivity
    nlinarith
  exact ⟨{
    relator := GGT.VanKampen.Embedded.dartWord Delta Gamma.sourceArc.rotated
    exterior := GGT.VanKampen.Embedded.dartWord Delta Gamma.sourceArc.darts
    remainder := sourceRemainder
    relator_decomposition := hsourceWord
    relator_mem := hsourceMem
    boundaryStart := outerArc.start.1
    boundaryStart_le := hstart
    boundaryArc := GGT.VanKampen.Embedded.dartWord Delta outerArc.darts
    boundaryAfter := boundaryAfter
    boundary_rotation_decomposition := hboundaryRotation
    leftSide := leftSide
    rightSide := rightSide
    leftSide_admissible := hleftGeo.1
    rightSide_admissible := hrightGeo.1
    leftSide_short := hleftLength
    rightSide_short := hrightLength
    exterior_value := by
      rw [hleftValue, hrightValue]
      exact harcs
    exterior_large := hlargeWeak }⟩

/-! ## The non-crossing based adapter -/

/-- A cyclic arc which ends before the selected basepoint is a literal factor
of the unrotated carrier. -/
theorem cyclic_prefix_decomposition_of_add_length_le
    {Alpha : Type*} {word arc after : List Alpha} {start : ℕ}
    (hstart : start ≤ word.length)
    (hrotation : word.rotate start = arc ++ after)
    (hfit : start + arc.length ≤ word.length) :
    word = word.take start ++ arc ++ word.drop (start + arc.length) := by
  have harcFits : arc.length ≤ (word.drop start).length := by
    rw [List.length_drop]
    omega
  have harc : (word.drop start).take arc.length = arc := by
    have hprefix : (word.rotate start).take arc.length = arc := by
      calc
        (word.rotate start).take arc.length =
            (arc ++ after).take arc.length := congrArg _ hrotation
        _ = arc := List.take_left
    rw [List.rotate_eq_drop_append_take hstart,
      List.take_append_of_le_length harcFits] at hprefix
    exact hprefix
  calc
    word = word.take start ++ word.drop start :=
      (List.take_append_drop start word).symm
    _ = word.take start ++
        ((word.drop start).take arc.length ++
          word.drop (start + arc.length)) := by
      rw [List.drop_take_append_drop]
    _ = word.take start ++ arc ++ word.drop (start + arc.length) := by
      rw [harc, List.append_assoc]

/-- A non-crossing embedded exterior arc gives the based cell object used by
the correction proof. -/
def Lemma49EmbeddedExteriorArc.toRelativeGreendlingerCell_of_not_crossing
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (E : Lemma49EmbeddedExteriorArc D v g n eps mu Z)
    (hfit : E.boundaryStart + E.boundaryArc.length ≤
      (lemma49BoundaryPower Z.boundaryWord n).length) :
    Lemma49RelativeGreendlingerCell D v g n eps mu Z := by
  let power := lemma49BoundaryPower Z.boundaryWord n
  have hsplit : power = List.take E.boundaryStart power ++ E.boundaryArc ++
      List.drop (E.boundaryStart + E.boundaryArc.length) power :=
    cyclic_prefix_decomposition_of_add_length_le E.boundaryStart_le
      E.boundary_rotation_decomposition hfit
  let contiguity : RelativeBoundaryContiguity D eps
      (List.map GGT.RelLetter.val power) E.relator := {
    exterior := E.exterior
    remainder := E.remainder
    relator_decomposition := E.relator_decomposition
    boundaryBefore := (List.take E.boundaryStart power).map GGT.RelLetter.val
    boundaryArc := E.boundaryArc.map GGT.RelLetter.val
    boundaryAfter :=
      (List.drop (E.boundaryStart + E.boundaryArc.length) power).map
        GGT.RelLetter.val
    boundary_decomposition := by
      have h := congrArg (List.map GGT.RelLetter.val) hsplit
      simpa only [List.map_append] using h
    leftSide := E.leftSide
    rightSide := E.rightSide
    leftSide_admissible := E.leftSide_admissible
    rightSide_admissible := E.rightSide_admissible
    leftSide_short := E.leftSide_short
    rightSide_short := E.rightSide_short
    exterior_value := by
      simpa only [GGT.RelLetter.listVal] using E.exterior_value }
  exact {
    relator := E.relator
    relator_mem := E.relator_mem
    contiguity := contiguity
    boundaryBefore := List.take E.boundaryStart power
    boundaryArc := E.boundaryArc
    boundaryAfter := List.drop (E.boundaryStart + E.boundaryArc.length) power
    boundary_decomposition := hsplit
    boundaryArc_value := rfl
    exterior_large := E.exterior_large }

end HullSC
end GroupApproximation
