import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalGFaceProve
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceChoose
import GroupApproximation.Meta.AxiomGuard

/-!
# Loop face sets for the face-set flip statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-52.

Route: a non-canonical choice of `F'` in `extremalGFaceProve_Clauses K F'`
(`Piece10Live/ExtremalGFaceProve`).  Let `A` be a simple closed walk that is a consecutive
stretch `c = p ++ A ++ q` of the walk `c` of `K`, and `S = sideFaces A` its side.  Three face
sets are read off `A` (`gfaceChoose_LoopFaces`):

* keep: `F' = S`, when the exterior face is not in `S`; the boundary darts of `F'` are `A`;
* inner excision: `F' = K.faces \ S`, when `S ⊆ K.faces`; the boundary darts are `p ++ q`;
* outer excision: `F' = K.faces ∪ sideOutside A`, when `K.faces ⊆ S` and the exterior face is
  in `S`; the boundary darts are again `p ++ q`.

Then six of the nine clauses are automatic (`gfaceChoose_of_loop`): no separation off the walk
and boundary darts on the walk (`Piece10Live/GFaceChoose`), the exterior face out, `F' ≠ K.faces`
(keep: from `¬Unpinched`, since `A` visits each vertex once; excision: the first dart of `A` is a
boundary dart of `K.faces` and not of `F'`), and the chain clause (keep: `A` is a walk; excision:
`p ++ q` is a walk since `A` closes up).  Left as the data of `gfaceChoose_Loop`: the source
face out, a cell in, and the two block clauses.

* `gfaceChoose_Loop K` (hypothesis): some stretch `A` and loop face set `F'` with those four.
* `gfaceChoose_of_loop` (proved): `gfaceChoose_Loop K` gives the face-set clauses.
* `gfaceChoose_Statement` (OPEN): `extremalGFaceProve_Statement` with `¬ gfaceChoose_Loop K`.
* `gfaceChoose_reduce` (proved): it implies `extremalGFaceProve_Statement`.
* `gfaceChoose_converse` (proved): the converse.

**LOUD: the residual is EQUIVALENT to `extremalGFaceProve_Statement`** (both directions
proved); it is smaller in proof content only, the loop cases being discharged.  **LOUD: the
loop construction is FALSE as a complete strategy**: there are premise-satisfying pockets with
no loop face set (truth check below), so the residual keeps genuine content.

## Truth check

Scratchpad `gl-p10-52/` (`loop.py` on the Lean-faithful `gl-p10-49/gface.py`, driven by
`drive.py`).  Mode `wind` (exactly the three face sets above, `A` any cyclic stretch):
subdivided gl-p10-40 models (as `gl-p10-49/sub49.py`), 242124 cases, 0 failures, also with
`A` restricted to non-wrapping stretches (`NOWRAP`, the Lean form `c = p ++ A ++ q`).  Random
maps: 7 runs, 4577526 cases, 15716 failures, nearly all with every candidate rejected at the
source clause; one minimal failure is a rose of four monogons that needs two non-consecutive
loops of opposite orientation excised together.  Earlier modes are FALSE too: `K.faces ∆ S`
(modes `keep`/`excise`) and single walk regions (`single.py`: 6 cases need a union).  The
general condition is a winding number (`c` minus several closed stretches), not formalized.
The searches do not model least area or labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap
open scoped Classical

section Loop

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The three loop face sets** at a closed stretch `A`: its side `S` without the exterior
face, `K.faces \ S` for `S ⊆ K.faces`, or `K.faces ∪ sideOutside A` for `K.faces ⊆ S` with the
exterior face in `S`. -/
def gfaceChoose_LoopFaces (K : PocketFaceSet D eps X lo hi) (A : List X.toCombMap.Dart)
    (F' : Finset X.toCombMap.Face) : Prop :=
  (F' = sideFaces X.toCombMap A ∧ X.outerFace ∉ F') ∨
  (F' = K.faces \ sideFaces X.toCombMap A ∧ sideFaces X.toCombMap A ⊆ K.faces) ∨
  (F' = K.faces ∪ sideOutside X.toCombMap A ∧ K.faces ⊆ sideFaces X.toCombMap A ∧
    X.outerFace ∈ sideFaces X.toCombMap A)

/-- **A loop choice of `F'`**: a simple closed stretch `A` of the walk and a loop face set `F'`
at `A` that misses the source face, holds a cell, and meets both arcs in one block. -/
def gfaceChoose_Loop (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (p A q : List X.toCombMap.Dart) (F' : Finset X.toCombMap.Face),
    K.boundary.cycle = p ++ A ++ q ∧ IsSimpleClosedWalk X.toCombMap A ∧
    gfaceChoose_LoopFaces K A F' ∧ (cell X K.source).face ∉ F' ∧
    (∃ kept : Fin X.rCellCount, (cell X kept).face ∈ F') ∧
    (∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
      K.sourceArc.darts.filter
        (fun d => extremalGFaceProve_bd X.toCombMap F' (X.toCombMap.alpha d)) = mid) ∧
    (∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
      K.targetArc.darts.filter (extremalGFaceProve_bd X.toCombMap F') = mid)

/-- **The face-set clauses from a loop choice.** -/
theorem gfaceChoose_of_loop (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hpinch : ¬Unpinched X.toCombMap K.faces) (h : gfaceChoose_Loop K) :
    ∃ F' : Finset X.toCombMap.Face, extremalGFaceProve_Clauses K F' := by
  obtain ⟨p, A, q, F', hseg, hw, hF, hsrc, hkept, h8, h9⟩ := h
  have hM := X.planar
  have hc := K.boundary.cycle_mem_iff
  have hAc : ∀ d ∈ A, d ∈ K.boundary.cycle := fun d hd => by
    rw [hseg]
    exact List.mem_append_left q (List.mem_append_right p hd)
  have hS := hw.isBoundaryDart_sideFaces_iff hM
  have hne_of : ∀ F : Finset X.toCombMap.Face,
      (∀ x, extremalGFaceProve_bd X.toCombMap F x = true ↔ x ∈ K.boundary.cycle ∧ x ∉ A) →
        F ≠ K.faces := by
    rintro F hb rfl
    have hd := List.head_mem hw.ne_nil
    have h1 : extremalGFaceProve_bd X.toCombMap K.faces (A.head hw.ne_nil) = true :=
      (extremalGFaceProve_bd_eq_true_iff _ _ _).mpr ((hc _).mp (hAc _ hd))
    exact ((hb _).mp h1).2 hd
  have key : ((∀ x, extremalGFaceProve_bd X.toCombMap F' x = true ↔ x ∈ A) ∨
      (∀ x, extremalGFaceProve_bd X.toCombMap F' x = true ↔ x ∈ K.boundary.cycle ∧ x ∉ A)) ∧
      X.outerFace ∉ F' ∧ F' ≠ K.faces := by
    rcases hF with ⟨rfl, hout⟩ | ⟨rfl, hSK⟩ | ⟨rfl, hKS, hOS⟩
    · refine ⟨Or.inl (gfaceChoose_bd_keep hw hM), hout, fun hK' => hpinch ?_⟩
      intro x y hx hy hxy
      rw [← hK'] at hx hy
      exact hw.vertexOf_inj ((hS x).mp hx) ((hS y).mp hy) hxy
    · have hb := gfaceChoose_bd_exciseIn hc hS hAc hSK
      exact ⟨Or.inr hb, fun h => K.outerFace_not_mem (Finset.mem_sdiff.mp h).1, hne_of _ hb⟩
    · have hb := gfaceChoose_bd_exciseOut hc hS hAc hKS (mem_sideOutside_iff X.toCombMap A)
      refine ⟨Or.inr hb, fun h => ?_, hne_of _ hb⟩
      rcases Finset.mem_union.mp h with h' | h'
      · exact K.outerFace_not_mem h'
      · exact (mem_sideOutside_iff X.toCombMap A _).mp h' hOS
  obtain ⟨hbd, hout, hne⟩ := key
  have hB : ∀ d, X.toCombMap.faceOf d ∈ F' → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ F' →
      d ∈ K.boundary.cycle := by
    intro d h1 h2
    have hd := (extremalGFaceProve_bd_eq_true_iff X.toCombMap F' d).mpr ⟨h1, h2⟩
    rcases hbd with hb | hb
    · exact hAc d ((hb d).mp hd)
    · exact ((hb d).mp hd).1
  have hnd := K.boundary.cycle_nodup
  have hch := hK.1
  rw [hseg] at hnd hch
  refine ⟨F', gfaceChoose_sep_of_bd hB, hB, hout, hsrc, hkept, hne, ?_, h8, h9⟩
  rw [hseg]
  rcases hbd with hb | hb
  · rw [gfaceChoose_filter_keep hnd hb]
    exact hw.chain
  · have hb' : ∀ x ∈ p ++ A ++ q, extremalGFaceProve_bd X.toCombMap F' x = true ↔ x ∉ A := by
      intro x hx
      refine (hb x).trans ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      rw [hseg]
      exact hx
    rw [gfaceChoose_filter_cut hnd hb']
    exact gfaceChoose_chain_cut hw.ne_nil hw.closes hch

end Loop

/-- **The face-set flip statement off the loop choices** (OPEN; EQUIVALENT to
`extremalGFaceProve_Statement`, see the module docstring).  Under the premises of
`extremalGFaceProve_Statement` and when no loop choice exists, some face set `F'` satisfies
`extremalGFaceProve_Clauses`. -/
def gfaceChoose_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
        ∃ F' : Finset X.toCombMap.Face, extremalGFaceProve_Clauses K F'

/-- **The face-set flip statement from its form off the loop choices.** -/
theorem gfaceChoose_reduce (h : gfaceChoose_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  rcases Classical.em (gfaceChoose_Loop K) with hL | hL
  · exact gfaceChoose_of_loop K hK hpinch hL
  · exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL

/-- **The form off the loop choices from the face-set flip statement** (the converse). -/
theorem gfaceChoose_converse (h : extremalGFaceProve_Statement.{u, w, v}) :
    gfaceChoose_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose _
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_LoopFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_Loop
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_of_loop
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_reduce
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceChoose.gfaceChoose_converse

