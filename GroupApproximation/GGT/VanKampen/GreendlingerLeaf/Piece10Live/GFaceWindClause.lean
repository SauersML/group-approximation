import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWind
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindClauseCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: clauses 4, 8 and 9 from the walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-57.

Route.  In a winding choice of `F'` (`gfaceWind_Choice`, `Piece10Live/GFaceWind`), the final
state `(c, g)` has `c` a sub-list of the walk `C = K.boundary.cycle`, `g` cobounded by `c` with
`g = 0` at the exterior face, and `C.filter (boundary dart of {g = 1}) = c` an `R`-chain
(`R d e : vertexOf (alpha d) = vertexOf e`).  Three of its open clauses then follow from
properties of `K` alone, for every such `(c, g)`:

* clause 4 (source face out) from `gfaceWindClause_SrcOut K`: the source face lies in the walk
  region of the exterior face (joined by steps across edges off the walk), since `g` is constant
  there (`gfaceWindClause_const`);
* clause 9 (target block) from `gfaceWindClause_TgtGap K`: the target arc, a suffix of `C`, is
  gap-free for `R` (`gfaceWindClause_block`);
* clause 8 (source block) from `gfaceWindClause_SrcGap K`: the source arc is gap-free for the
  relation `R` transported through `invDarts` (reverse, then `alpha`).

* `gfaceWindClause_Choice K` (hypothesis): `gfaceWind_Choice K` with clauses 4, 8 and 9 each
  weakened to a disjunction with the corresponding walk property.
* `gfaceWindClause_choice` (proved): it gives `gfaceWind_Choice K`; the converse
  `gfaceWindClause_of_choice` is immediate.
* `gfaceWindClause_Statement` (OPEN): `gfaceWind_Statement` with conclusion
  `gfaceWindClause_Choice K`.
* `gfaceWindClause_reduce` (proved): it implies `gfaceWind_Statement`;
  `gfaceWindClause_extremal`: hence `extremalGFaceProve_Statement`.
* `gfaceWindClause_of_statement` (proved): the converse, from `gfaceWind_Statement`.

**LOUD: the residual is EQUIVALENT to `gfaceWind_Statement`, not strictly weaker** (both
directions are proved here).  It is **strictly smaller in proof content**: on every pocket with
`SrcOut ∧ SrcGap ∧ TgtGap` (a property of `K`, no `F'`), clauses 4, 8 and 9 are discharged and
only a nonempty excision sequence to a `0/1`-valued `g` with a kept cell in its support remains.
Clauses 4, 5, 8 and 9 are NOT closed in general: when the walk properties fail the residual
still asks for them.  No contiguity is assumed: gap-freeness is a condition on the arc darts
and the walk, and the block property is derived from the chain clause.

## Truth check

Scratchpad `gl-p10-57/clause.py`, on the Lean-faithful models of `gl-p10-49/gface.py`,
`gl-p10-52/loop.py` and the integer reach of `gl-p10-55/wind.py`: random maps, seed 1, 60 s,
8339 instances, 1107666 pocket decompositions, 19619360 reached `0/1` states.  `SrcOut` implies
the source face out: 0 failures.  Gap-free source (resp. target) arc and chain filter imply one
block: 0 failures (both are also proved here).  Frequencies: `SrcOut` 257221, source gap-free
1106191, target gap-free 1106295, all three 256417 of 1107666 decompositions; non-block states
occur only on non-gap-free arcs (9862 source, 11432 target).  The search does not model least
area or labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

section Clause

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The source face in the exterior walk region**: the exterior face reaches the source face
by steps across edges off the walk. -/
def gfaceWindClause_SrcOut (K : PocketFaceSet D eps X lo hi) : Prop :=
  Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap K.boundary.cycle) X.outerFace
    (cell X K.source).face

/-- **A gap-free source arc**, for the walk relation transported through `invDarts`. -/
def gfaceWindClause_SrcGap (K : PocketFaceSet D eps X lo hi) : Prop :=
  gfaceWindClause_Gap
    (fun a b => X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha b)) =
      X.toCombMap.vertexOf (X.toCombMap.alpha a))
    K.sourceArc.darts

/-- **A gap-free target arc**, for the walk relation. -/
def gfaceWindClause_TgtGap (K : PocketFaceSet D eps X lo hi) : Prop :=
  gfaceWindClause_Gap (fun a b => X.toCombMap.vertexOf (X.toCombMap.alpha a) =
    X.toCombMap.vertexOf b) K.targetArc.darts

/-- **A winding choice with walk-discharged clauses**: `gfaceWind_Choice K` with clauses 4, 8
and 9 each replaced by its disjunction with `SrcOut`, `SrcGap`, `TgtGap`. -/
def gfaceWindClause_Choice (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (c : List X.toCombMap.Dart) (g : X.toCombMap.Face → ℤ),
    Relation.TransGen (gfaceWind_Step X.toCombMap X.outerFace)
      (K.boundary.cycle, gfaceWind_ind K.faces) (c, g) ∧
    (∀ f, g f = 0 ∨ g f = 1) ∧
    (gfaceWindClause_SrcOut K ∨ (cell X K.source).face ∉ gfaceWind_faces g) ∧
    (∃ kept : Fin X.rCellCount, (cell X kept).face ∈ gfaceWind_faces g) ∧
    (gfaceWindClause_SrcGap K ∨
      ∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
        K.sourceArc.darts.filter (fun d =>
          extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g) (X.toCombMap.alpha d)) = mid) ∧
    (gfaceWindClause_TgtGap K ∨
      ∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
        K.targetArc.darts.filter (extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g)) = mid)

/-- **The converse**: a winding choice is one with walk-discharged clauses. -/
theorem gfaceWindClause_of_choice (K : PocketFaceSet D eps X lo hi)
    (h : gfaceWind_Choice K) : gfaceWindClause_Choice K := by
  obtain ⟨c, g, hr, h01, h4, h5, h8, h9⟩ := h
  exact ⟨c, g, hr, h01, Or.inr h4, h5, Or.inr h8, Or.inr h9⟩

/-- **Clauses 4, 8 and 9 from the walk**: a winding choice with walk-discharged clauses is a
winding choice. -/
theorem gfaceWindClause_choice (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (h : gfaceWindClause_Choice K) : gfaceWind_Choice K := by
  obtain ⟨c, g, hr, h01, h4, hkept, h8, h9⟩ := h
  have hc := K.boundary.cycle_mem_iff
  have h0 : gfaceWind_Inv X.toCombMap K.boundary.cycle X.outerFace K.boundary.cycle
      (gfaceWind_ind K.faces) :=
    gfaceWind_inv_start (fun d => (hc d).symm) hK.1 K.outerFace_not_mem
  obtain ⟨⟨hfil, hch, hcob, ho⟩, -⟩ :=
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
  have hfeq :
      K.boundary.cycle.filter (extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g)) = c := by
    rw [← hfil]
    exact List.filter_congr fun x _ =>
      extremalGFaceProve_bool_eq_of_true_iff ((hbd x).trans gfaceWind_mem_eq_true_iff.symm)
  have hch2 : (K.boundary.cycle.filter
      (extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g))).IsChain
      (fun d e => X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) := by
    rw [hfeq]
    exact hch
  rw [K.decomposition] at hch2
  simp only [List.filter_append] at hch2
  refine ⟨c, g, hr, h01, ?_, hkept, ?_, ?_⟩
  · rcases h4 with hs | hs
    · intro hmem
      rw [gfaceWind_mem_faces, ← gfaceWindClause_const hsub hcob hs, ho] at hmem
      norm_num at hmem
    · exact hs
  · rcases h8 with hs | hs
    · have hB := hch2.left_of_append.left_of_append.right_of_append
      have h1 : (invDarts X K.sourceArc.darts).filter
          (extremalGFaceProve_bd X.toCombMap (gfaceWind_faces g)) =
          ((K.sourceArc.darts.filter fun d => extremalGFaceProve_bd X.toCombMap
            (gfaceWind_faces g) (X.toCombMap.alpha d)).reverse).map X.toCombMap.alpha := by
        unfold invDarts
        rw [List.filter_map, List.filter_reverse] <;> rfl
      rw [h1, List.isChain_map, List.isChain_reverse] at hB
      exact gfaceWindClause_block hs hB
    · exact hs
  · rcases h9 with hs | hs
    · exact gfaceWindClause_block hs hch2.right_of_append
    · exact hs

end Clause

/-- **The winding flip statement with walk-discharged clauses** (OPEN; EQUIVALENT to
`gfaceWind_Statement`, both directions proved, strictly smaller in proof content, see the
module docstring).  Under the premises of `extremalGFaceProve_Statement`, a winding choice of
`F'` with walk-discharged clauses 4, 8 and 9 exists. -/
def gfaceWindClause_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → gfaceWindClause_Choice K

/-- **The winding flip statement from its walk-discharged form.** -/
theorem gfaceWindClause_reduce (h : gfaceWindClause_Statement.{u, w, v}) :
    gfaceWind_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact gfaceWindClause_choice K hK
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose)

/-- **The face-set flip statement from the walk-discharged form.** -/
theorem gfaceWindClause_extremal (h : gfaceWindClause_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} :=
  gfaceWind_reduce (gfaceWindClause_reduce h)

/-- **The converse**: the winding flip statement gives its walk-discharged form. -/
theorem gfaceWindClause_of_statement (h : gfaceWind_Statement.{u, w, v}) :
    gfaceWindClause_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact gfaceWindClause_of_choice K
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_SrcOut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_SrcGap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_TgtGap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_Choice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_of_choice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_choice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_reduce
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_extremal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_of_statement

