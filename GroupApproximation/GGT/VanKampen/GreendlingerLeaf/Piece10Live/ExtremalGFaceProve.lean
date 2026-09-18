import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalGFaceProveCore
import GroupApproximation.Meta.AxiomGuard

/-!
# The G-face tolerant flip statement as a face-set statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-49.

Route: a colouring `z` in `extremalGFace_Clauses K z` is traded for the face set
`F' = flipFaces X.toCombMap K.faces z` (`Piece10Live/ExtremalGFaceProveCore`).  Five of the ten
clauses become automatic:

* constancy along the walk regions: from "`F'` separates no dart off the walk"
  (`extremalGFaceProve_colour_step`);
* no doubly flipped side pair: from "every boundary dart of `F'` is on the walk"
  (`extremalGFaceProve_colour_indep`);
* the three face memberships are read on `F'` itself (`extremalGFaceProve_flipFaces_colour`);
* the touch clause: `F' ≠ K.faces` in a connected map (`extremalGFaceProve_touch`);
* non-emptiness of the kept darts: `F'` holds a cell face and misses the exterior face, so it
  has a boundary dart (`extremalGFaceProve_filter_bd_ne_nil`).

The kept darts of the colour on the walk are the boundary darts of `F'`
(`extremalGFaceProve_movePred_colour_of_mem`), so the chain and the two block clauses are read
on `extremalGFaceProve_bd X.toCombMap F'`.

* `extremalGFaceProve_Clauses K F'` (face-set form): `F'` separates no dart off the walk, has
  its boundary darts on the walk, holds a cell face and neither the exterior nor the source
  face, differs from `K.faces`, and its boundary darts on the walk are a chain and a block on
  each arc.
* `extremalGFaceProve_Statement` (OPEN): under the premises of `extremalGFace_Statement`, some
  `F'` satisfies `extremalGFaceProve_Clauses`.
* `extremalGFaceProve_extremalGFace` (proved): it implies `extremalGFace_Statement`.
* `extremalGFaceProve_of_extremalGFace` (proved): the converse.

**LOUD: the residual is EQUIVALENT to `extremalGFace_Statement`** (both directions proved).  A
strictly weaker residual with a proved reduction into the target cannot exist; this one is
smaller in proof content only: constancy, independence, touch, non-emptiness and the flipped
memberships are discharged, and what is left is the choice of `F'` with the chain and the two
block clauses.

## Truth check

Scratchpad `gl-p10-49/` (Lean-faithful `gface.py`; the search asks for the Lean clauses plus
closure of the kept walk and a decrease of repeated visits, which is stronger).
`search3.py` in the G-face regime (at least two inner walk regions): 4 runs, 98007670 cases,
0 failures (614 of them need a union of regions, all on witness-seeded maps).  `sub49.py` on
the gl-p10-48 subdivided gl-p10-40 models (edges `{2,3},{6,7},{8,9},{12,13}`, every non-empty
subset, 1 to 3 subdivisions, `eps` 1, 2 and unbounded, source and kept cell fixed or free):
270 configurations, 238488 cases, 0 failures; in up to 256 cases per configuration no single
region works and a union of two regions is needed.  The canonical colourings are
FALSE: "flip every free region" fails 3028035 times and "flip every inner region but the kept
one" fails 127309 times (`canon.py`), so the choice of `F'` is genuinely open.  The searches do
not model least area or labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Clauses

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The face-set clauses**: `F'` separates no dart off the walk, has its boundary darts on the
walk, keeps the exterior and source faces out and a relator cell in, differs from `K.faces`, and
its boundary darts on the walk form a walk in cycle order and one block on each arc (read through
`alpha` on the source arc, whose inverse darts are on the walk). -/
def extremalGFaceProve_Clauses (K : PocketFaceSet D eps X lo hi)
    (F' : Finset X.toCombMap.Face) : Prop :=
  (∀ x, ¬ walkKeep X.toCombMap K.boundary.cycle x →
    (X.toCombMap.faceOf x ∈ F' ↔ X.toCombMap.faceOf (X.toCombMap.alpha x) ∈ F')) ∧
  (∀ d, X.toCombMap.faceOf d ∈ F' → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ F' →
    d ∈ K.boundary.cycle) ∧
  X.outerFace ∉ F' ∧ (cell X K.source).face ∉ F' ∧
  (∃ kept : Fin X.rCellCount, (cell X kept).face ∈ F') ∧ F' ≠ K.faces ∧
  ((K.boundary.cycle.filter (extremalGFaceProve_bd X.toCombMap F')).IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
  (∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
    K.sourceArc.darts.filter
      (fun d => extremalGFaceProve_bd X.toCombMap F' (X.toCombMap.alpha d)) = mid) ∧
  (∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
    K.targetArc.darts.filter (extremalGFaceProve_bd X.toCombMap F') = mid)

/-- The inverse of a source-arc dart is on the walk. -/
theorem extremalGFaceProve_alpha_mem_of_source (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.sourceArc.darts) :
    X.toCombMap.alpha d ∈ K.boundary.cycle := by
  have hinv : X.toCombMap.alpha d ∈ invDarts X K.sourceArc.darts := by
    show X.toCombMap.alpha d ∈ K.sourceArc.darts.reverse.map X.toCombMap.alpha
    exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
  rw [K.decomposition]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hinv))

/-- A target-arc dart is on the walk. -/
theorem extremalGFaceProve_mem_of_target (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.targetArc.darts) :
    d ∈ K.boundary.cycle := by
  rw [K.decomposition]
  exact List.mem_append_right _ hd

/-- **The G-face tolerant clauses from the face-set clauses**, at the colour of `F'`. -/
theorem extremalGFaceProve_clauses_of (K : PocketFaceSet D eps X lo hi)
    {F' : Finset X.toCombMap.Face} (h : extremalGFaceProve_Clauses K F') :
    extremalGFace_Clauses K (extremalGFaceProve_colour X.toCombMap K.faces F') := by
  obtain ⟨hU, hB, hout, hsrc, ⟨kept, hkept⟩, hne, hch, ⟨pre₁, mid₁, post₁, hs₁, hf₁⟩,
    ⟨pre₂, mid₂, post₂, hs₂, hf₂⟩⟩ := h
  have hc := K.boundary.cycle_mem_iff
  have hz := extremalGFaceProve_colour_step X.toCombMap K.faces F' hc hU
  have hflip := extremalGFaceProve_flipFaces_colour hz
  have hconn := CombMap.connected_of_planar X.toCombMap X.planar
  have hC : K.boundary.cycle.filter
      (movePred X.toCombMap (extremalGFaceProve_colour X.toCombMap K.faces F')) =
      K.boundary.cycle.filter (extremalGFaceProve_bd X.toCombMap F') :=
    List.filter_congr fun d hd => extremalGFaceProve_movePred_colour_of_mem hc hd
  refine ⟨hz, extremalGFaceProve_colour_indep hc hB, (by rw [hflip]; exact hout),
    (by rw [hflip]; exact hsrc), ⟨kept, by rw [hflip]; exact hkept⟩,
    extremalGFaceProve_touch hconn K.boundary.cycle_nonempty hz hne,
    (by rw [hC]; exact extremalGFaceProve_filter_bd_ne_nil hconn hB hkept hout),
    (by rw [hC]; exact hch), ⟨pre₁, mid₁, post₁, hs₁, ?_⟩, ⟨pre₂, mid₂, post₂, hs₂, ?_⟩⟩
  · refine Eq.trans (List.filter_congr fun d hd => ?_) hf₁
    exact (P10ExtremalResidual.movePred_alpha X.toCombMap _ d).symm.trans
      (extremalGFaceProve_movePred_colour_of_mem hc
        (extremalGFaceProve_alpha_mem_of_source K hd))
  · refine Eq.trans (List.filter_congr fun d hd => ?_) hf₂
    exact extremalGFaceProve_movePred_colour_of_mem hc (extremalGFaceProve_mem_of_target K hd)

/-- **The face-set clauses from the G-face tolerant clauses**, at the flipped face set. -/
theorem extremalGFaceProve_of_clauses (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart → Bool} (h : extremalGFace_Clauses K z) :
    extremalGFaceProve_Clauses K (flipFaces X.toCombMap K.faces z) := by
  obtain ⟨hz, hind, hout, hsrc, hkept, ⟨y, hy, hpy⟩, -, hch, ⟨pre₁, mid₁, post₁, hs₁, hf₁⟩,
    ⟨pre₂, mid₂, post₂, hs₂, hf₂⟩⟩ := h
  have hc := K.boundary.cycle_mem_iff
  have hC : K.boundary.cycle.filter
      (extremalGFaceProve_bd X.toCombMap (flipFaces X.toCombMap K.faces z)) =
      K.boundary.cycle.filter (movePred X.toCombMap z) :=
    List.filter_congr fun d hd => (extremalGFaceProve_movePred_flip hc hz hd).symm
  refine ⟨fun x hk => extremalGFaceProve_flip_union hc hz x hk,
    fun d h1 h2 => extremalGFaceProve_flip_boundary hc hz hind d h1 h2, hout, hsrc, hkept,
    extremalGFaceProve_flip_ne hc hz hy hpy, (by rw [hC]; exact hch),
    ⟨pre₁, mid₁, post₁, hs₁, ?_⟩, ⟨pre₂, mid₂, post₂, hs₂, ?_⟩⟩
  · refine Eq.trans (List.filter_congr fun d hd => ?_) hf₁
    exact (extremalGFaceProve_movePred_flip hc hz
      (extremalGFaceProve_alpha_mem_of_source K hd)).symm.trans
        (P10ExtremalResidual.movePred_alpha X.toCombMap z d)
  · refine Eq.trans (List.filter_congr fun d hd => ?_) hf₂
    exact (extremalGFaceProve_movePred_flip hc hz (extremalGFaceProve_mem_of_target K hd)).symm

end Clauses

/-- **The face-set form of the G-face tolerant flip statement** (OPEN; EQUIVALENT to
`extremalGFace_Statement`, see the module docstring).  Under the premises of
`extremalGFace_Statement`, some face set `F'` satisfies `extremalGFaceProve_Clauses`. -/
def extremalGFaceProve_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ F' : Finset X.toCombMap.Face, extremalGFaceProve_Clauses K F'

/-- **The G-face tolerant flip statement from its face-set form.** -/
theorem extremalGFaceProve_extremalGFace (h : extremalGFaceProve_Statement.{u, w, v}) :
    extremalGFace_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨F', hF⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨extremalGFaceProve_colour X.toCombMap K.faces F', extremalGFaceProve_clauses_of K hF⟩

/-- **The face-set form from the G-face tolerant flip statement** (the converse). -/
theorem extremalGFaceProve_of_extremalGFace (h : extremalGFace_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨z, hz⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨flipFaces X.toCombMap K.faces z, extremalGFaceProve_of_clauses K hz⟩

/-- **Osin's Lemma 4.4 at least-area diagrams from the four-piece-off residual and the face-set
form of the G-face tolerant flip statement.** -/
theorem extremalGFaceProve_relativeGreendlinger
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : extremalGFaceProve_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalGFace_relativeGreendlinger hoff (extremalGFaceProve_extremalGFace h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_Clauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_alpha_mem_of_source
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_mem_of_target
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_clauses_of
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_of_clauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_extremalGFace
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_of_extremalGFace
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_relativeGreendlinger
