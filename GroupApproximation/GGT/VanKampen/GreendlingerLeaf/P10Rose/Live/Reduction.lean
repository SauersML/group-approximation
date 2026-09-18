import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.InPlace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Move
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Reduction.InPlace
import GroupApproximation.Meta.AxiomGuard

/-!
# The live rose reduction chain, part 2: the sub-arc region move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  New-file replacement of `P10Rose/Proof` and
`P10Rose/SubArc` without the filter route (dead-route removal, part 2).  The in-place gap
`RoseInPlaceStepStatement`, its reductions `combinatorialStep_of_inPlaceStep`, `rose_of_inPlaceStep`
and `exists_succ_of_isClosedDartWalk` live in `P10Rose/Live/Reduction/InPlace` (re-exported by this
module); this module reduces `RoseInPlaceStepStatement` to `RoseRegionMoveSubArcStatement`, a
colouring claim with no pocket conclusion, and proves `inPlaceStep_of_regionMoveSubArc` and
`rose_of_regionMoveSubArc`.  The walk-rotation and flip-move API (`FilterWalk.exists_rotation`,
`FilterMove.movePred`, `flipFaces`, `isBoundaryDart_flipFaces_iff`) comes from `P10Rose/Live/Move`.

## Removed dead route (FALSE statements)

`RoseFilterStepStatement` (old `P10Rose/InPlaceFilter`) and `RoseRegionMoveStatement` (old
`P10Rose/FilterMove`) were FALSE because they keep both arcs: the three-petal flower
`c = [p₃] ++ [q₃] ++ [p₁, q₁, p₂] ++ [q₂]` has no step keeping `t₂` entire.  They were removed,
together with `inPlaceStep_of_filterStep` and `rose_of_filterStep`; nothing here imports them.

## The corrected move

Flip regions, which may also remove arc darts.  The new cycle is re-listed as
`s₁' ++ t₁'⁻¹ ++ s₂' ++ t₂'` with new proper arcs `t₁'` (on a possibly new source cell) and `t₂'`,
new sides of length `≤ ε`, a possibly new kept cell, and `lo ≤ start t₂'`,
`start t₂' + |t₂'| ≤ hi`.  The listing only has to be a permutation of the filtered cycle that is a
closed walk, so non-contiguous lobes (`step_of_lobe`) are covered too.

*The reduction.*  `isBoundaryDart_flipFaces_iff` identifies the boundary.  Some kept dart shares
its vertex with a removed dart: rotate the old cycle so that it ends in a kept dart `e` and starts
with a removed dart `f` (`FilterWalk.exists_rotation`), so `α e` ends where `f` begins; the
successor of `e` in the new closed walk begins there too (`exists_succ_of_isClosedDartWalk`).
Then `step_of_faces`.

## Why the statement is expected to be true

* *All in-place tools fit.*  A face set `F'` with `∂F' ⊆ c` is `flipFaces F z` with
  `z d = (face d ∈ F) xor (face d ∈ F')`; `z` is region-constant and never flips both sides of a
  dart of `c`.  A step with `∂F' = c` keeps `repeatedVisits`, so some dart must be removed.
* *Flower test*: `z = true` exactly on the region `{p₂, q₂}` of `P₂`; `F' = {P₁, P₃}`, source `S`,
  kept `P₁`, `s₁' = [p₃]`, `t₁' = t₁`, `s₂' = [p₁, q₁]`, `t₂' = zeroArc t₂`; the listing is the
  filter `[p₃, q₃, p₁, q₁]`, a closed walk, and `y = p₂` is removed.
* *Risk.*  The argument is not a proof: a configuration where every extremal region contains a
  middle block of `t₁⁻¹` or `t₂`, or a wrapping `t₂` whose new start drops below `lo`.  The search
  of the in-flight lane found neither.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides FilterMove

/-- **A region move with sub-arcs for the rose step** (OPEN; the isolated remaining claim of
`P10Rose`).  Under the hypotheses of `RoseInPlaceStepStatement`, some region-constant dart
colouring `z` that never flips both sides of a dart of the cycle keeps the exterior face out and
removes some dart of the cycle, and the kept darts can be listed, as a closed dart walk, in the form
`s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` for a source cell outside and a kept cell inside the moved face set, proper
arcs `t₁`, `t₂`, sides of length at most `ε` and `lo ≤ start t₂`, `start t₂ + |t₂| ≤ hi`.  See the
module docstring for the argument that it is true and for the tests it passes. -/
def RoseRegionMoveSubArcStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ z : X.toCombMap.Dart → Bool,
          (∀ x y, CombMap.FaceClassStep X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y) ∧
          (∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false) ∧
          X.outerFace ∉ flipFaces X.toCombMap K.faces z ∧
          (∃ y ∈ K.boundary.cycle, movePred X.toCombMap z y = false) ∧
          ∃ (source kept : Fin X.rCellCount),
            (cell X source).face ∉ flipFaces X.toCombMap K.faces z ∧
            (cell X kept).face ∈ flipFaces X.toCombMap K.faces z ∧
            ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
              (s₁ s₂ : List X.toCombMap.Dart),
              List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
                (K.boundary.cycle.filter (movePred X.toCombMap z)) ∧
              IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
              s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi ∧
              t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

/-- **The in-place rose step from a sub-arc region move**, by `step_of_faces`. -/
theorem inPlaceStep_of_regionMoveSubArc (h : RoseRegionMoveSubArcStatement.{u, w, v}) :
    RoseInPlaceStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨z, hz, hind, hout, ⟨y, hy, hpy⟩, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hLperm,
    hwalk, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hw : IsClosedDartWalk X.toCombMap K.boundary.cycle :=
    ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  have hbd := isBoundaryDart_flipFaces_iff K.boundary.cycle_mem_iff hz hind
  have hmem : ∀ d, d ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ↔
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap (flipFaces X.toCombMap K.faces z) d :=
    fun d => (hLperm.mem_iff.trans List.mem_filter).trans (hbd d).symm
  have hperm : List.Perm K.boundary.cycle ((s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ++
      K.boundary.cycle.filter (fun d => !movePred X.toCombMap z d)) :=
    (List.filter_append_perm (movePred X.toCombMap z) K.boundary.cycle).symm.trans
      (hLperm.symm.append_right _)
  have hneL : s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ≠ [] := by
    obtain ⟨hne, -⟩ := hwalk
    exact hne
  have hx₀ := List.mem_filter.mp (hLperm.mem_iff.mp (List.head_mem hneL))
  obtain ⟨A, B, hne, hAB, hlast, hhead⟩ := FilterWalk.exists_rotation (movePred X.toCombMap z)
    hx₀.1 hx₀.2 hy hpy
  have hwAB : IsClosedDartWalk X.toCombMap (A ++ B) := by
    rw [← hAB]
    exact hw
  obtain ⟨_hne', -, hclose⟩ := hwAB.append_comm
  have hmemc : ∀ d ∈ B ++ A, d ∈ K.boundary.cycle := by
    intro d hd
    rw [hAB]
    exact List.mem_append.mpr (List.mem_append.mp hd).symm
  have he : (B ++ A).getLast hne ∈ s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts :=
    hLperm.mem_iff.mpr (List.mem_filter.mpr ⟨hmemc _ (List.getLast_mem hne), hlast⟩)
  obtain ⟨x, hx, hxv⟩ := exists_succ_of_isClosedDartWalk hwalk he
  have hy' : (B ++ A).head hne ∈ K.boundary.cycle.filter (fun d => !movePred X.toCombMap z d) :=
    List.mem_filter.mpr ⟨hmemc _ (List.head_mem hne), by simp only [hhead, Bool.not_false]⟩
  exact step_of_faces K hlabel hout hsource hkept hmem hs₁ hs₂ hlo hhi ht₁ ht₂ hwalk hperm hx hy'
    (hxv.symm.trans hclose)

/-- **The rose step from a sub-arc region move.** -/
theorem rose_of_regionMoveSubArc (h : RoseRegionMoveSubArcStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  rose_of_inPlaceStep (inPlaceStep_of_regionMoveSubArc h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.inPlaceStep_of_regionMoveSubArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.rose_of_regionMoveSubArc
