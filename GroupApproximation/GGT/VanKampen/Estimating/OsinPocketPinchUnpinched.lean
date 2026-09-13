import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionUnpinched
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch at an unpinched pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  `PocketPinchStatement` asks for an O-equivalent copy with a simple
pocket face set.  A pocket face set whose boundary cycle follows the boundary and visits no vertex
twice is already simple, so the diagram itself is the copy.  A simple pocket face set visits no
vertex twice.  What remains of the pinch is a pocket face set whose cycle does not follow the
boundary, or has a repeated vertex.

* `PocketFaceSet.simple_of_followsBoundary`: an unpinched pocket face set whose cycle follows the
  boundary is simple.
* `PocketFaceSet.unpinched_of_simple`: a simple pocket face set is unpinched.
* `PocketFaceSet.exists_simple_of_followsBoundary`: the conclusion of `PocketPinchStatement` for
  such a pocket, with the identity O-equivalence.
* `PocketPinchPinchedStatement` and `pocketPinchStatement_of_pinched`: the pinch reduces to pocket
  face sets whose cycle does not follow the boundary or is pinched.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Surgery.MapCollapse

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **An unpinched pocket that follows the boundary is simple.** -/
theorem simple_of_followsBoundary (K : PocketFaceSet D eps X lo hi)
    (hwalk : K.boundary.FollowsBoundary) (hpinch : Unpinched X.toCombMap K.faces) : K.Simple :=
  K.boundary.isSimpleClosedWalk_of_followsBoundary hwalk hpinch

/-- **A simple pocket is unpinched.** -/
theorem unpinched_of_simple (K : PocketFaceSet D eps X lo hi) (hK : K.Simple) :
    Unpinched X.toCombMap K.faces :=
  K.boundary.unpinched_of_isSimpleClosedWalk hK

/-- **The pinch at an unpinched pocket.**  The diagram itself is the O-equivalent copy. -/
theorem exists_simple_of_followsBoundary (K : PocketFaceSet D eps X lo hi)
    (hwalk : K.boundary.FollowsBoundary) (hpinch : Unpinched X.toCombMap K.faces) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple :=
  ⟨X, K, ⟨OEquivalentDiscDiagram.refl X⟩, K.simple_of_followsBoundary hwalk hpinch⟩

end PocketFaceSet

/-- **The pinch at a pinched pocket**: `PocketPinchStatement` for the pocket face sets whose
boundary cycle does not follow the boundary, or visits a vertex twice. -/
def PocketPinchPinchedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ)
    (K : PocketFaceSet D eps X lo hi),
    ¬(K.boundary.FollowsBoundary ∧ Unpinched X.toCombMap K.faces) →
      ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
        Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple

/-- **The pinch reduces to pinched pockets.** -/
theorem pocketPinchStatement_of_pinched (h : PocketPinchPinchedStatement.{u, w, v}) :
    PocketPinchStatement.{u, w, v} := by
  intro G _ Lambda D eps W X lo hi K
  by_cases hK : K.boundary.FollowsBoundary ∧ Unpinched X.toCombMap K.faces
  · exact K.exists_simple_of_followsBoundary hK.1 hK.2
  · exact h D eps W X lo hi K hK

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.unpinched_of_simple
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_simple_of_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchStatement_of_pinched
