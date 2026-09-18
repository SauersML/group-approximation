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
  gfaceWindClause_Gap (fun a b => X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha b)) =
    X.toCombMap.vertexOf (X.toCombMap.alpha a)) K.sourceArc.darts

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

