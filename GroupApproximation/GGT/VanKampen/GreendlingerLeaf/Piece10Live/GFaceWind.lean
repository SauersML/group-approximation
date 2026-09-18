import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalGFaceProve
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindReach
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'` for the face-set flip statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-55.

Route: a non-canonical, multi-stretch choice of `F'` in `extremalGFaceProve_Clauses K F'`
(`Piece10Live/ExtremalGFaceProve`).  Start from `(c, g) = (K.boundary.cycle, [· ∈ K.faces])` and
repeatedly excise a simple closed stretch `W` of the current walk `c` (inner or wrapping), each
time subtracting the winding function of `W` normalised at the exterior face
(`gfaceWind_Step`, `Piece10Live/GFaceWindStep`).  Along any such sequence `c` stays a sub-walk of
the walk, `g` stays cobounded by `c` and vanishes at the exterior face, and `c` gets shorter
(`gfaceWind_reach_pair`, `Piece10Live/GFaceWindReach`).  When the final `g` is `0/1`-valued, its
support `F' = {g = 1}` has boundary darts exactly `c`, so five clauses are automatic:
no separation off the walk, boundary darts on the walk, the exterior face out, `F' ≠ K.faces`
(`c` is strictly shorter than the walk), and the chain clause (`c` is a walk).

* `gfaceWind_Choice K` (hypothesis): a nonempty excision sequence ending in a `0/1`-valued `g`
  whose support misses the source face, holds a cell, and meets both arcs in one block.
* `gfaceWind_of_choice` (proved): `gfaceWind_Choice K` gives the face-set clauses.
* `gfaceWind_Statement` (OPEN): `extremalGFaceProve_Statement` with conclusion
  `gfaceWind_Choice K`.
* `gfaceWind_reduce` (proved): it implies `extremalGFaceProve_Statement`.

**LOUD: the residual is NOT strictly weaker.**  Mathematically it is EQUIVALENT to
`extremalGFaceProve_Statement` (any valid `F'` has boundary darts a sub-walk `c'` of the walk;
the gaps of `c'` split into consecutive simple closed stretches and a coboundary on a connected
map is determined up to a constant), but only the direction residual ⇒ target is proved here,
so in Lean it is stronger-or-equal.  It is smaller in proof content: clauses 1, 2, 3, 6 and 7
are discharged, without `¬Unpinched`.  **LOUD: the face-set version is FALSE**: iterating the
three loop face sets of `Piece10Live/GFaceChooseLoop` on face sets instead of integer winding
sums fails (truth check below); only the integer bookkeeping is complete.

## Truth check

Scratchpad `gl-p10-55/` (`wind.py`, `rose.py`, on the Lean-faithful `gl-p10-49/gface.py` and
`gl-p10-52/loop.py`); a case passes when some state reached in at least one step satisfies the
face-set clauses.  Integer mode (this statement), 0 failures throughout: random and witness maps,
KEPT=every (each kept face), 134866126 cases; KEPT=exists (the Lean clause), 38811819 cases,
with the subdivided gl-p10-40 models; roses of three and four monogons, 839040 cases.  Face-set
mode: FAIL (random seed 21: 4022 of 546999; seed 37: 480 of 24042; rose of four monogons: 15360
of 837888).  The searches do not model least area or labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

section Wind

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A winding choice of `F'`**: a nonempty excision sequence from the walk of `K` and the
indicator of its faces to a `0/1`-valued `g`, whose support misses the source face, holds a
cell, and meets both arcs in one block. -/
def gfaceWind_Choice (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (c : List X.toCombMap.Dart) (g : X.toCombMap.Face → ℤ),
    Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) ∧
    (∀ f, g f = 0 ∨ g f = 1) ∧ (cell X K.source).face ∉ gfaceWind_faces g ∧
    (∃ kept : Fin X.rCellCount, (cell X kept).face ∈ gfaceWind_faces g) ∧
    (∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
      K.sourceArc.darts.filter (fun d =>
        extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g) (X.toCombMap.alpha d)) = mid) ∧
    (∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
      K.targetArc.darts.filter (extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g)) = mid)

/-- **The face-set clauses from a winding choice.** -/
theorem gfaceWind_of_choice (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (h : gfaceWind_Choice K) :
    ∃ F' : Finset X.toCombMap.Face, extremalGFaceProve_Clauses K F' := by
  obtain ⟨c, g, hr, h01, hsrc, hkept, h8, h9⟩ := h
  have hc := K.boundary.cycle_mem_iff
  have h0 : gfaceWind_Inv X.toCombMap K.boundary.cycle X.outerFace K.boundary.cycle
      (gfaceWind_ind K.faces) :=
    gfaceWind_inv_start (fun d => (hc d).symm) hK.1 K.outerFace_not_mem
  obtain ⟨⟨hfil, hch, hcob, ho⟩, hlen⟩ :=
    gfaceWind_reach_pair X.planar K.boundary.cycle_nodup hr h0
  have hsub : ∀ x ∈ c, x ∈ K.boundary.cycle := by
    intro x hx
    have hx' : x ∈ K.boundary.cycle.filter (gfaceWind_mem c) := by
      rw [hfil]
      exact hx
    exact (List.mem_filter.mp hx').1
  have hne : ∀ x, x ∈ c → X.toCombMap.alpha x ∉ c := fun x hx hax =>
    ((hc x).mp (hsub x hx)).2 ((hc _).mp (hsub _ hax)).1
  have hbd : ∀ x,
      extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g) x = true ↔ x ∈ c := by
    intro x
    rw [extremalGFaceProve_bd_eq_true_iff, gfaceWind_mem_faces, gfaceWind_mem_faces]
    exact gfaceWind_bd_iff (hcob x) (h01 _) (h01 _) (hne x)
  have hB : ∀ d, X.toCombMap.faceOf d ∈ gfaceWind_faces g →
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ gfaceWind_faces g →
        d ∈ K.boundary.cycle := fun d h1 h2 =>
    hsub d ((hbd d).mp ((extremalGFaceProve_bd_eq_true_iff _ _ _).mpr ⟨h1, h2⟩))
  refine ⟨gfaceWind_faces g, gfaceChoose_sep_of_bd hB, hB, ?_, hsrc, hkept, ?_, ?_, h8, h9⟩
  · rw [gfaceWind_mem_faces, ho]
    norm_num
  · intro hF
    have hall : ∀ x ∈ K.boundary.cycle, gfaceWind_mem c x = true := by
      intro x hx
      refine gfaceWind_mem_eq_true_iff.mpr ((hbd x).mp ?_)
      rw [hF, extremalGFaceProve_bd_eq_true_iff]
      exact (hc x).mp hx
    have hCc : K.boundary.cycle = c := by
      rw [← hfil]
      exact (List.filter_eq_self.mpr hall).symm
    rw [hCc] at hlen
    exact lt_irrefl _ hlen
  · have hfeq :
        K.boundary.cycle.filter (extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g)) = c := by
      rw [← hfil]
      exact List.filter_congr fun x _ =>
        extremalGFaceProve_bool_eq_of_true_iff ((hbd x).trans gfaceWind_mem_eq_true_iff.symm)
    rw [hfeq]
    exact hch

end Wind

/-- **The face-set flip statement in winding form** (OPEN; mathematically EQUIVALENT to
`extremalGFaceProve_Statement`, only one direction proved, see the module docstring).  Under
the premises of `extremalGFaceProve_Statement`, a winding choice of `F'` exists. -/
def gfaceWind_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → gfaceWind_Choice K

/-- **The face-set flip statement from its winding form.** -/
theorem gfaceWind_reduce (h : gfaceWind_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact gfaceWind_of_choice K hK
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_Choice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_of_choice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWind_reduce

