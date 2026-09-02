import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.GGT.VanKampen.Estimating.Selection

/-!
# Embedded contiguity regions in a relative disc diagram

This file defines the finite geometric objects used in Osin's Appendix
Definition M.  An embedded region is a finite set of faces of one fixed disc
diagram.  Every selected face is a `G`-cell.  Its boundary consists of the
darts based in the face set whose reversed darts are based outside it.

A boundary traversal is split into a cyclic arc on a relator cell, a right
side, the oppositely oriented cyclic arc on either another relator cell or the
outer boundary, and a left side.  Cyclic arcs include their start positions.
Both side words have length and word norm at most `eps`.

Candidates are subtypes of `Finset Delta.toCombMap.Face`, so they form a
finite type.  Pairwise compatibility is disjointness of face sets, and the
finite maximization theorem in `Estimating.Selection` produces the
distinguished family of Definition M.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.WordMetric

universe u w v

namespace Embedded

/-! ## Words and oriented carrier boundaries -/

/-- The word read on a list of darts in the ambient disc diagram. -/
def dartWord
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (darts : List Delta.toCombMap.Dart) :
    List (GGT.RelLetter G Lambda) :=
  darts.map Delta.label

/-- The relator cell at an index in the stored cell order. -/
def cell
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    RelatorCell Delta.toCombMap Delta.outerFace W :=
  Delta.relatorCells.get i

/-- An indexed cell belongs to the stored relator-cell list. -/
theorem cell_mem
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    cell Delta i ∈ Delta.relatorCells := by
  exact List.get_mem Delta.relatorCells i

/-- The dart cycle on the boundary of an indexed relator cell. -/
def cellDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    List Delta.toCombMap.Dart :=
  (Delta.faceBoundary (cell Delta i).face).darts

/-- The word on `cellDarts` is the stored relator word. -/
theorem dartWord_cellDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    dartWord Delta (cellDarts Delta i) = (cell Delta i).word := by
  symm
  exact Delta.relatorCell_word (cell Delta i) (cell_mem Delta i)

/-- Darts of the outer boundary oriented as the boundary of the disc rather
than as the boundary of the distinguished outer face. -/
def outerDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) : List Delta.toCombMap.Dart :=
  (Delta.faceBoundary Delta.outerFace).darts.reverse.map Delta.toCombMap.alpha

/-- The word on the oriented outer darts is `Delta.boundaryWord`. -/
theorem dartWord_outerDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) :
    dartWord Delta (outerDarts Delta) = Delta.boundaryWord := by
  simp only [dartWord, outerDarts, List.map_map, DiscDiagram.boundaryWord,
    DiscDiagram.faceWord, HullSC.RelWord.revInv, List.map_reverse]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro d hd
  exact Delta.label_alpha d

/-- The second carrier of an embedded contiguity region.  `none` denotes the
oriented outer boundary; `some i` denotes the `i`-th relator cell. -/
def targetDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (target : Option (Fin Delta.rCellCount)) : List Delta.toCombMap.Dart :=
  match target with
  | none => outerDarts Delta
  | some i => cellDarts Delta i

/-! ## Cyclic arcs with base positions -/

/-- A cyclic subarc of a finite dart cycle.  The start index is allowed to
equal the cycle length, which is the same base position as zero and keeps the
empty-cycle case finite. -/
structure CyclicArc {Dart : Type v} (cycle : List Dart) where
  start : Fin (cycle.length + 1)
  length : ℕ
  length_le : length ≤ cycle.length

namespace CyclicArc

/-- Rotate a cycle to the chosen base position. -/
def rotated {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) :
    List Dart :=
  cycle.drop arc.start.1 ++ cycle.take arc.start.1

/-- The explicit drop-take rotation agrees with `List.rotate`. -/
theorem rotated_eq_rotate {Dart : Type v} {cycle : List Dart}
    (arc : CyclicArc cycle) : arc.rotated = cycle.rotate arc.start.1 := by
  have hstart : arc.start.1 ≤ cycle.length := by omega
  exact (List.rotate_eq_drop_append_take hstart).symm

/-- Darts in the chosen cyclic subarc. -/
def darts {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) :
    List Dart :=
  arc.rotated.take arc.length

/-- Rotation preserves the length of the ambient cycle. -/
theorem rotated_length {Dart : Type v} {cycle : List Dart}
    (arc : CyclicArc cycle) : arc.rotated.length = cycle.length := by
  rw [rotated, List.length_append, List.length_drop, List.length_take]
  have hstart : arc.start.1 ≤ cycle.length := by omega
  omega

/-- The stored length is the actual number of darts in the arc. -/
theorem darts_length {Dart : Type v} {cycle : List Dart}
    (arc : CyclicArc cycle) : arc.darts.length = arc.length := by
  rw [darts, List.length_take, arc.rotated_length]
  exact Nat.min_eq_left arc.length_le

/-- A cyclic subarc of a duplicate-free carrier has no repeated darts. -/
theorem darts_nodup {Dart : Type v} {cycle : List Dart}
    (arc : CyclicArc cycle) (hcycle : cycle.Nodup) : arc.darts.Nodup := by
  rw [darts, arc.rotated_eq_rotate]
  exact (List.nodup_rotate.mpr hcycle).sublist (List.take_sublist _ _)

/-- Reversing every dart and reversing the order gives the opposite
orientation of an arc. -/
def reverseDarts {M : CombMap} {cycle : List M.Dart}
    (arc : CyclicArc cycle) : List M.Dart :=
  arc.darts.reverse.map M.alpha

end CyclicArc

/-- The cyclic carrier of a relator cell has no repeated darts. -/
theorem cellDarts_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    (cellDarts Delta i).Nodup :=
  (Delta.faceBoundary (cell Delta i).face).nodup

/-- The target arc as it occurs on the boundary of the selected G-cell face
set.  `outerDarts` is already oriented from the diagram side of the outer
face.  A relator-cell target, like the source cell, must instead be crossed
by `alpha` and read in reverse order. -/
def targetBoundaryDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (target : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta target)) :
    List Delta.toCombMap.Dart :=
  match target with
  | none => arc.darts
  | some _ => arc.reverseDarts

/-! ## Boundaries of face sets -/

/-- A dart lies on the boundary of a face set when it is based in a selected
face and its reverse is based in an unselected face. -/
def IsBoundaryDart
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) (d : Delta.toCombMap.Dart) : Prop :=
  Delta.toCombMap.faceOf d ∈ faces ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∉ faces

/-- The finite set of boundary darts of a face set. -/
noncomputable def boundaryDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) : Finset Delta.toCombMap.Dart := by
  classical
  exact Finset.univ.filter fun d => IsBoundaryDart Delta faces d

/-- Membership in `boundaryDarts` is the boundary-dart predicate. -/
theorem mem_boundaryDarts_iff
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) (d : Delta.toCombMap.Dart) :
    d ∈ boundaryDarts Delta faces ↔ IsBoundaryDart Delta faces d := by
  classical
  simp only [boundaryDarts, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Crossing an internal edge and advancing around the adjacent selected
face is one elementary move while tracing the boundary of a face set. -/
def InternalBoundaryMove
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face)
    (d e : Delta.toCombMap.Dart) : Prop :=
  Delta.toCombMap.faceOf d ∈ faces ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ faces ∧
      e = Delta.toCombMap.facePerm (Delta.toCombMap.alpha d)

/-- Successive boundary darts are obtained by advancing once around the
current face and then crossing zero or more internal edges. -/
def BoundaryStep
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face)
    (d e : Delta.toCombMap.Dart) : Prop :=
  IsBoundaryDart Delta faces d ∧ IsBoundaryDart Delta faces e ∧
    Relation.ReflTransGen (InternalBoundaryMove Delta faces)
      (Delta.toCombMap.facePerm d) e

/-- A cyclic enumeration of the boundary of a G-cell-only face set. -/
structure FaceSetBoundary
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) where
  faces_nonempty : faces.Nonempty
  all_gCells : ∀ face ∈ faces,
    face ≠ Delta.outerFace ∧ GGT.RelLetter.listVal (Delta.faceWord face) = 1
  cycle : List Delta.toCombMap.Dart
  cycle_nonempty : cycle ≠ []
  cycle_nodup : cycle.Nodup
  cycle_mem_iff : ∀ d : Delta.toCombMap.Dart,
    d ∈ cycle ↔ IsBoundaryDart Delta faces d
  cycle_chain : cycle.IsChain (BoundaryStep Delta faces)
  cycle_closes : BoundaryStep Delta faces
    (cycle.getLast cycle_nonempty) (cycle.head cycle_nonempty)

/-! ## Embedded contiguity candidates -/

/-- A contiguity region embedded in `Delta`.  The source is a relator cell;
the target is either a relator cell or the oriented outer boundary. -/
structure Contiguity
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) where
  boundary : FaceSetBoundary Delta faces
  source : Fin Delta.rCellCount
  target : Option (Fin Delta.rCellCount)
  sourceArc : CyclicArc (cellDarts Delta source)
  targetArc : CyclicArc (targetDarts Delta target)
  rightSide : List Delta.toCombMap.Dart
  leftSide : List Delta.toCombMap.Dart
  boundary_decomposition : boundary.cycle =
    sourceArc.reverseDarts ++ rightSide ++
      targetBoundaryDarts Delta target targetArc ++ leftSide
  rightSide_length_le : rightSide.length ≤ eps
  leftSide_length_le : leftSide.length ≤ eps
  rightSide_norm_le : wordNorm D.alphabet.carrier
    (GGT.RelLetter.listVal (dartWord Delta rightSide)) ≤ eps
  leftSide_norm_le : wordNorm D.alphabet.carrier
    (GGT.RelLetter.listVal (dartWord Delta leftSide)) ≤ eps

namespace Contiguity

/-- Crossing a dart of the source cell arc enters a face of the embedded
G-cell region. -/
theorem faceOf_alpha_mem_of_mem_sourceArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (d : Delta.toCombMap.Dart) (hd : d ∈ Gamma.sourceArc.darts) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ faces := by
  have hreverse : Delta.toCombMap.alpha d ∈ Gamma.sourceArc.reverseDarts := by
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨d, hd, rfl⟩
  have hcycle : Delta.toCombMap.alpha d ∈ Gamma.boundary.cycle := by
    rw [Gamma.boundary_decomposition]
    simp only [List.mem_append]
    exact Or.inl hreverse
  exact (Gamma.boundary.cycle_mem_iff (Delta.toCombMap.alpha d)).mp hcycle |>.1

/-- When the target is a relator cell, crossing a dart of its target arc also
enters a face of the embedded G-cell region. -/
theorem faceOf_alpha_mem_of_mem_targetArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target)
    (d : Delta.toCombMap.Dart) (hd : d ∈ Gamma.targetArc.darts) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ faces := by
  have hreverse : Delta.toCombMap.alpha d ∈ Gamma.targetArc.reverseDarts := by
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨d, hd, rfl⟩
  have htargetBoundary : Delta.toCombMap.alpha d ∈
      targetBoundaryDarts Delta Gamma.target Gamma.targetArc := by
    rw [targetBoundaryDarts, htarget]
    exact hreverse
  have hcycle : Delta.toCombMap.alpha d ∈ Gamma.boundary.cycle := by
    rw [Gamma.boundary_decomposition]
    simp only [List.mem_append]
    exact Or.inr (Or.inr (Or.inl htargetBoundary))
  exact (Gamma.boundary.cycle_mem_iff (Delta.toCombMap.alpha d)).mp hcycle |>.1

end Contiguity

/-- A face set is a candidate when it admits embedded contiguity data. -/
def IsCandidate
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) : Prop :=
  Nonempty (Contiguity D eps Delta faces)

/-- The empty face set is not an embedded contiguity candidate. -/
theorem not_isCandidate_empty
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) :
    ¬ IsCandidate D eps Delta ∅ := by
  rintro ⟨Gamma⟩
  exact Finset.not_nonempty_empty Gamma.boundary.faces_nonempty

/-- The finite type of embedded face-set candidates. -/
def Candidate
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) :=
  {faces : Finset Delta.toCombMap.Face // IsCandidate D eps Delta faces}

noncomputable instance candidateFintype
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W} :
    Fintype (Candidate D eps Delta) := by
  classical
  exact Fintype.ofFinset
    (Finset.univ.filter fun faces => IsCandidate D eps Delta faces)
    (fun faces => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl)

noncomputable instance candidateDecidableEq
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W} :
    DecidableEq (Candidate D eps Delta) :=
  Classical.decEq _

/-- Choose the embedded data certified by a candidate face set. -/
noncomputable def Candidate.contiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (candidate : Candidate D eps Delta) :
    Contiguity D eps Delta candidate.1 :=
  Classical.choice candidate.2

/-- Two candidates are compatible exactly when their ambient face sets are
disjoint. -/
def Compatible
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (first second : Candidate D eps Delta) : Prop :=
  Disjoint first.1 second.1

/-- Definition M maximizes the total lengths of both contiguity arcs. -/
noncomputable def Candidate.weight
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (candidate : Candidate D eps Delta) : ℕ :=
  candidate.contiguity.sourceArc.length + candidate.contiguity.targetArc.length

/-- The finite maximization of Definition M produces a distinguished family
of pairwise face-disjoint embedded regions. -/
theorem exists_distinguishedFamily
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) :
    Nonempty (EstimatingSelection.DistinguishedFamily
      (Compatible (D := D) (eps := eps) (Delta := Delta))
      (Candidate.weight (D := D) (eps := eps) (Delta := Delta))) := by
  exact EstimatingSelection.exists_distinguishedFamily
    (Compatible (D := D) (eps := eps) (Delta := Delta))
    (Candidate.weight (D := D) (eps := eps) (Delta := Delta))

/-! ## G-cell surgery and Lemma 65(a) -/

/-- An `O`-equivalent replacement of a G-cell-only region inside one ambient
diagram.  Both face sets have disc boundaries consisting only of G-cells, and
the two oriented boundary words agree.  This is the face-set form of the
local surgery used in Osin's Appendix: the relator cells and the outer
boundary of the ambient diagram are untouched. -/
structure GCellReplacement
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (oldFaces newFaces : Finset Delta.toCombMap.Face) where
  oldBoundary : FaceSetBoundary Delta oldFaces
  newBoundary : FaceSetBoundary Delta newFaces
  boundaryWord_eq :
    dartWord Delta oldBoundary.cycle = dartWord Delta newBoundary.cycle

/-- Union of two candidate face carriers.  It is noncomputable only because
the quotient face type does not carry a global decidable-equality instance. -/
noncomputable def candidateFaceUnion
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (first second : Candidate D eps Delta) : Finset Delta.toCombMap.Face := by
  letI : DecidableEq Delta.toCombMap.Face := Classical.decEq _
  exact first.1 ∪ second.1

/-- The surgery which merges two embedded regions.  Its old carrier is the
union of their face sets and its new carrier is the candidate chosen to
replace them. -/
structure MergeSurgery
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (first second merged : Candidate D eps Delta) where
  replacement : GCellReplacement Delta (candidateFaceUnion first second) merged.1
  mergedFace_mem : ∀ face : Delta.toCombMap.Face,
    face ∈ merged.1 ↔ face ∈ first.1 ∨ face ∈ second.1

/-- Compatibility of embedded regions is symmetric. -/
theorem compatible_symm
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {first second : Candidate D eps Delta}
    (h : Compatible first second) : Compatible second first := by
  exact h.symm

/-- A merged face set is disjoint from any candidate disjoint from each of
its two constituents. -/
theorem compatible_merge
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {first second merged other : Candidate D eps Delta}
    (surgery : MergeSurgery first second merged)
    (hfirst : Compatible first other)
    (hsecond : Compatible second other) : Compatible merged other := by
  classical
  change Disjoint first.1 other.1 at hfirst
  change Disjoint second.1 other.1 at hsecond
  change Disjoint merged.1 other.1
  apply Finset.disjoint_left.mpr
  intro face hface hother
  have hfirst' := Finset.disjoint_left.mp hfirst
  have hsecond' := Finset.disjoint_left.mp hsecond
  rcases (surgery.mergedFace_mem face).mp hface with hface | hface
  · exact hfirst' hface hother
  · exact hsecond' hface hother

/-- Replacing two selected embedded regions by their merged surgery preserves
pairwise face-disjointness of the distinguished family. -/
theorem merge_replacement_pairwise
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : EstimatingSelection.DistinguishedFamily
      (Compatible (D := D) (eps := eps) (Delta := Delta))
      (Candidate.weight (D := D) (eps := eps) (Delta := Delta)))
    (first second merged : Candidate D eps Delta)
    (hfirst : first ∈ selected.family)
    (hsecond : second ∈ selected.family)
    (surgery : MergeSurgery first second merged) :
    EstimatingSelection.PairwiseCompatible
      (Compatible (D := D) (eps := eps) (Delta := Delta))
      (insert merged ((selected.family.erase first).erase second)) := by
  classical
  have member_cases : ∀ candidate : Candidate D eps Delta,
      candidate ∈ insert merged ((selected.family.erase first).erase second) →
        candidate = merged ∨
          (candidate ∈ selected.family ∧ candidate ≠ first ∧ candidate ≠ second) := by
    intro candidate hcandidate
    rcases Finset.mem_insert.mp hcandidate with hmerged | hrest
    · exact Or.inl hmerged
    · have hsecondData := Finset.mem_erase.mp hrest
      have hfirstData := Finset.mem_erase.mp hsecondData.2
      exact Or.inr ⟨hfirstData.2, hfirstData.1, hsecondData.1⟩
  intro a ha b hb hab
  rcases member_cases a ha with haMerged | haOld
  · rcases member_cases b hb with hbMerged | hbOld
    · exact (hab (haMerged.trans hbMerged.symm)).elim
    · subst a
      have hfirstb := selected.pairwise first hfirst b hbOld.1 hbOld.2.1.symm
      have hsecondb := selected.pairwise second hsecond b hbOld.1 hbOld.2.2.symm
      exact compatible_merge surgery hfirstb hsecondb
  · rcases member_cases b hb with hbMerged | hbOld
    · subst b
      have hfirsta := selected.pairwise first hfirst a haOld.1 haOld.2.1.symm
      have hseconda := selected.pairwise second hsecond a haOld.1 haOld.2.2.symm
      exact compatible_symm (compatible_merge surgery hfirsta hseconda)
    · exact selected.pairwise a haOld.1 b hbOld.1 hab

/-- A genuine union merge cannot already be one of the untouched selected
regions: it contains every face of the nonempty first region, whereas the
selected family makes those two face sets disjoint. -/
theorem merged_not_mem_rest
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : EstimatingSelection.DistinguishedFamily
      (Compatible (D := D) (eps := eps) (Delta := Delta))
      (Candidate.weight (D := D) (eps := eps) (Delta := Delta)))
    (first second merged : Candidate D eps Delta)
    (hfirst : first ∈ selected.family)
    (surgery : MergeSurgery first second merged) :
    merged ∉ (selected.family.erase first).erase second := by
  classical
  intro hmerged
  have hmergedData := Finset.mem_erase.mp hmerged
  have hmergedFirst := Finset.mem_erase.mp hmergedData.2
  have hdisjoint := selected.pairwise first hfirst merged
    hmergedFirst.2 hmergedFirst.1.symm
  obtain ⟨face, hface⟩ := first.contiguity.boundary.faces_nonempty
  have hfaceMerged : face ∈ merged.1 := by
    exact (surgery.mergedFace_mem face).mpr (Or.inl hface)
  exact (Finset.disjoint_left.mp hdisjoint) hface hfaceMerged

/-- **Lemma 65(a), two-gon consequence.**  Two selected regions cannot admit
an `O`-equivalent G-cell-only union replacement whose two contiguity arcs have
at least their combined length.  Thus every parallel two-gon surviving the
Definition M selection contains a relator cell; otherwise its G-cell faces
give precisely such a merge surgery. -/
theorem lemma65a_no_mergeable_twoGon
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : EstimatingSelection.DistinguishedFamily
      (Compatible (D := D) (eps := eps) (Delta := Delta))
      (Candidate.weight (D := D) (eps := eps) (Delta := Delta)))
    (first second merged : Candidate D eps Delta)
    (hfirst : first ∈ selected.family)
    (hsecond : second ∈ selected.family)
    (hne : first ≠ second)
    (surgery : MergeSurgery first second merged)
    (hweight : first.weight + second.weight ≤ merged.weight) : False := by
  classical
  let rest := (selected.family.erase first).erase second
  let replacement := insert merged rest
  have hsecondRest : second ∈ selected.family.erase first :=
    Finset.mem_erase.mpr ⟨hne.symm, hsecond⟩
  have hfirstWeight :
      EstimatingSelection.familyWeight Candidate.weight
          (selected.family.erase first) + first.weight =
        EstimatingSelection.familyWeight Candidate.weight selected.family := by
    unfold EstimatingSelection.familyWeight
    exact Finset.sum_erase_add selected.family Candidate.weight hfirst
  have hsecondWeight :
      EstimatingSelection.familyWeight Candidate.weight rest + second.weight =
        EstimatingSelection.familyWeight Candidate.weight
          (selected.family.erase first) := by
    dsimp [rest]
    unfold EstimatingSelection.familyWeight
    exact Finset.sum_erase_add (selected.family.erase first) Candidate.weight hsecondRest
  have hmergedRest := merged_not_mem_rest selected first second merged hfirst surgery
  have hreplacementWeight :
      EstimatingSelection.familyWeight Candidate.weight replacement =
        merged.weight + EstimatingSelection.familyWeight Candidate.weight rest := by
    dsimp [replacement]
    unfold EstimatingSelection.familyWeight
    rw [Finset.sum_insert hmergedRest]
  have htotal :
      EstimatingSelection.familyWeight Candidate.weight selected.family ≤
        EstimatingSelection.familyWeight Candidate.weight replacement := by
    rw [hreplacementWeight]
    omega
  have hcardFirst : (selected.family.erase first).card + 1 =
      selected.family.card := Finset.card_erase_add_one hfirst
  have hcardSecond : rest.card + 1 =
      (selected.family.erase first).card := by
    dsimp [rest]
    exact Finset.card_erase_add_one hsecondRest
  have hcardReplacement : replacement.card = rest.card + 1 := by
    dsimp [replacement]
    rw [Finset.card_insert_of_notMem hmergedRest]
  have hcard : replacement.card < selected.family.card := by omega
  exact EstimatingSelection.not_weight_ge_and_card_lt selected replacement
    (merge_replacement_pairwise selected first second merged hfirst hsecond surgery)
    ⟨htotal, hcard⟩

end Embedded

end VanKampen
end GGT
end GroupApproximation
