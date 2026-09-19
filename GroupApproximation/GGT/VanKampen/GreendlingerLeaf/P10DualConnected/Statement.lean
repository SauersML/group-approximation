import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The disjunctive dual-connectivity invariant of a pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane ms-nm-uncond-b, for lane nm-gl03d's
invariant route to residual (ii).

A set of faces is **dual-connected off a walk `C`** when any two of its faces are joined by moves
that go around a face or cross an edge not on `C`: the equivalence closure of
`CombMap.FaceClassStep M (walkKeep M C)`.  Such moves never cross an edge of `C`, so for the
boundary cycle of a face set `F` they stay inside `F` or inside its complement.

* `p10DC_FacesDualConnected M F C`: the faces of `F` are dual-connected off `C`.
* `p10DC_ComplementDualConnected M F C`: the faces off `F` are dual-connected off `C`.
* `p10DC_Invariant M F C`: one of the two.
* `p10DC_PocketInvariant K`: the invariant for a pocket face set with its boundary cycle.

Lane ms-nm-partial-a proved the core of residual (ii) on paper in two cases: when `F` is
dual-connected, and when its complement is.  So the invariant is the hypothesis under which that
proof applies.  Whether the initial pocket of the waist induction satisfies it is checked on paper
on nm-gl03d's board.  The verdict there is that it can fail.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, residual 10).  It certifies
no printed sentence on its own.  Definitions only: nothing here is a hypothesis of a consumer yet.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10DualConnected

universe u w v

open SimpleClosedWalkSides

section Map

variable (M : CombMap.{v})

/-- **Dual-connected off a walk.**  Any two faces satisfying `S` contain darts joined by moves
around a face or across an edge not on `C`. -/
def p10DC_DualConnected (C : List M.Dart) (S : M.Face → Prop) : Prop :=
  ∀ f g : M.Face, S f → S g → ∃ x y : M.Dart, M.faceOf x = f ∧ M.faceOf y = g ∧
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M C)) x y

/-- **The faces of `F` are dual-connected off `C`.** -/
def p10DC_FacesDualConnected (F : Finset M.Face) (C : List M.Dart) : Prop :=
  p10DC_DualConnected M C (fun f => f ∈ F)

/-- **The faces off `F` are dual-connected off `C`.** -/
def p10DC_ComplementDualConnected (F : Finset M.Face) (C : List M.Dart) : Prop :=
  p10DC_DualConnected M C (fun f => f ∉ F)

/-- **The disjunctive invariant**: `F` or its complement is dual-connected off `C`. -/
def p10DC_Invariant (F : Finset M.Face) (C : List M.Dart) : Prop :=
  p10DC_FacesDualConnected M F C ∨ p10DC_ComplementDualConnected M F C

end Map

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The invariant for a pocket face set**, off its boundary cycle. -/
def p10DC_PocketInvariant (K : PocketFaceSet D eps X lo hi) : Prop :=
  p10DC_Invariant X.toCombMap K.faces K.boundary.cycle

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10DualConnected

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10DualConnected.p10DC_DualConnected
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10DualConnected.p10DC_Invariant
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10DualConnected.p10DC_PocketInvariant
