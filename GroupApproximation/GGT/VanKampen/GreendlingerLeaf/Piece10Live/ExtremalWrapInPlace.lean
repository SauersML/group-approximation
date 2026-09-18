import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapCore
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal.Close
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# The in-place rose step without wrap, from the no-wrap extremal core

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-12a.

The existing chain `RoseExtremalCoreStatement → RoseExtremalJunctionStatement →
RoseExtremalRegionStatement → RoseSingleRegionMoveStatement → RoseRegionMoveSubArcStatement →
RoseInPlaceStepStatement` consumes whole statements, so it cannot be fed a statement that carries
the extra premise `hi ≤ |outerDarts X|`.  This module states the in-place step with that premise
and proves it from `RoseExtremalCoreNoWrapStatement` pointwise, by the same argument.

* `step_of_regionMove` (proved): the body of `P10Rose.inPlaceStep_of_regionMoveSubArc` as a
  pointwise lemma, for one pocket and one flip colouring `z`.
* `RoseInPlaceStepNoWrapStatement`: `P10Rose.RoseInPlaceStepStatement` with the premise
  `hi ≤ |outerDarts X|`; `inPlaceStepNoWrap_of_inPlaceStep` (proved) shows it is implied by the
  original.
* `inPlaceStepNoWrap_of_extremalCoreNoWrap` (proved): the composite of the existing reductions
  (connectedness clause, region colouring, closing the listing, flip at the region), pointwise.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Pointwise

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The in-place step from one region move**, pointwise (body of
`P10Rose.inPlaceStep_of_regionMoveSubArc`). -/
theorem step_of_regionMove (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {z : X.toCombMap.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y)
    (hind : ∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false)
    (hout : X.outerFace ∉ flipFaces X.toCombMap K.faces z)
    {y : X.toCombMap.Dart} (hy : y ∈ K.boundary.cycle) (hpy : movePred X.toCombMap z y = false)
    {source kept : Fin X.rCellCount}
    (hsource : (cell X source).face ∉ flipFaces X.toCombMap K.faces z)
    (hkept : (cell X kept).face ∈ flipFaces X.toCombMap K.faces z)
    {t₁ : CyclicArc (cellDarts X source)} {t₂ : CyclicArc (outerDarts X)}
    {s₁ s₂ : List X.toCombMap.Dart}
    (hLperm : List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
      (K.boundary.cycle.filter (movePred X.toCombMap z)))
    (hwalk : IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts))
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) (hlo : lo ≤ t₂.start.1)
    (hhi : t₂.start.1 + t₂.length ≤ hi)
    (ht₁ : t₁.length < (cellDarts X source).length) (ht₂ : t₂.length < (outerDarts X).length) :
    ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
      K'.sourceArc.length < (cellDarts X K'.source).length ∧
      K'.targetArc.length < (outerDarts X).length ∧ K'.repeatedVisits < K.repeatedVisits := by
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
  obtain ⟨A, B, hne, hAB, hlast, hhead⟩ :=
    P10Rose.FilterWalk.exists_rotation (movePred X.toCombMap z) hx₀.1 hx₀.2 hy hpy
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
  obtain ⟨x, hx, hxv⟩ := P10Rose.exists_succ_of_isClosedDartWalk hwalk he
  have hy' : (B ++ A).head hne ∈ K.boundary.cycle.filter (fun d => !movePred X.toCombMap z d) :=
    List.mem_filter.mpr ⟨hmemc _ (List.head_mem hne), by simp only [hhead, Bool.not_false]⟩
  exact P10Rose.step_of_faces K hlabel hout hsource hkept hmem hs₁ hs₂ hlo hhi ht₁ ht₂ hwalk hperm
    hx hy' (hxv.symm.trans hclose)

end Pointwise

/-- **The in-place rose step without wrap**: `P10Rose.RoseInPlaceStepStatement` with the premise
`hi ≤ |outerDarts X|`. -/
def RoseInPlaceStepNoWrapStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
          K'.sourceArc.length < (cellDarts X K'.source).length ∧
          K'.targetArc.length < (outerDarts X).length ∧
          K'.repeatedVisits < K.repeatedVisits

/-- **The no-wrap in-place step is implied by the original one.** -/
theorem inPlaceStepNoWrap_of_inPlaceStep (h : P10Rose.RoseInPlaceStepStatement.{u, w, v}) :
    RoseInPlaceStepNoWrapStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi _ hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose

/-- **The no-wrap in-place step from the no-wrap extremal core**: the existing reduction chain,
pointwise. -/
theorem inPlaceStepNoWrap_of_extremalCoreNoWrap (h : RoseExtremalCoreNoWrapStatement.{u, w, v}) :
    RoseInPlaceStepNoWrapStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hne, hs₁c, hs₂c,
      hj₁, hj₂, hj₃, hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨y, hy, hry⟩ := P10RegionMove.exists_mem_eqvGen_of_connected
    (CombMap.connected_of_planar X.toCombMap X.planar) K.boundary.cycle_nonempty r
  have hz := regionColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r
  have hind := regionColour_indep K.boundary.cycle_mem_iff r
  have hwalk := P10RoseExtremal.isClosedDartWalk_of_perm_filter K.boundary.cycle_nodup
    K.boundary.cycle_mem_iff hz hind hperm hne
    (P10RoseExtremalTrim.isChain_listing_of_junctions t₁ t₂ hs₁c hs₂c hj₁ hj₂ hj₃)
  exact step_of_regionMove K hK hlabel hz hind
    (not_mem_flipFaces hz K.outerFace_not_mem
      (fun x hx => regionColour_eq_false X.toCombMap _ (hrout x hx)))
    hy (movePred_regionColour_eq_false hry) hsource hkept hperm hwalk hs₁ hs₂ hlo hhi ht₁ ht₂

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.step_of_regionMove
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.RoseInPlaceStepNoWrapStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.inPlaceStepNoWrap_of_inPlaceStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.inPlaceStepNoWrap_of_extremalCoreNoWrap
