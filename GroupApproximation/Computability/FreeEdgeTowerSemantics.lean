import GroupApproximation.Computability.FreeEdgeTowerCode
import GroupApproximation.Algebra.HNNCongr
import GroupApproximation.Algebra.HNNPresentation
import GroupApproximation.Algebra.PresentedGroupRelabel
import GroupApproximation.Higman.ExplicitFreeEdge

/-!
# One-edge semantics for the raw free-edge compiler

This file connects one `FreeEdgeTowerCode.edgeCode` layer to the honest HNN
extension built by `Higman.ExplicitFreeEdge`.  The only algebraic hypotheses
are injectivity of the two displayed evaluations from the free group on the
finite edge list.  No MF permanence claim is made here.
-/

namespace GroupApproximation
namespace FreeEdgeTowerSemantics

open PresentationCodes FreeEdgeTowerCode
open Higman ExplicitFreeEdge

/-- The relator set presented by a code, named for use with
`HNNPresentation`. -/
abbrev codeRels (c : PresentationCode) :
    Set (FreeGroup (Fin (genCount c))) :=
  ((relatorFinset c : Finset (FreeGroup (Fin (genCount c)))) :
    Set (FreeGroup (Fin (genCount c))))

/-- The source word of the `i`-th raw edge. -/
def sourceWord (c : PresentationCode) (edges : List (Raw × Raw))
    (i : Fin edges.length) : FreeGroup (Fin (genCount c)) :=
  wordOf c (edges.get i).1

/-- The target word of the `i`-th raw edge. -/
def targetWord (c : PresentationCode) (edges : List (Raw × Raw))
    (i : Fin edges.length) : FreeGroup (Fin (genCount c)) :=
  wordOf c (edges.get i).2

/-- Evaluate the free source tuple in the group presented by `c`. -/
def sourceEval (c : PresentationCode) (edges : List (Raw × Raw)) :
    FreeGroup (Fin edges.length) →* Carrier c :=
  FreeGroup.lift fun i => PresentedGroup.mk (codeRels c) (sourceWord c edges i)

/-- Evaluate the free target tuple in the group presented by `c`. -/
def targetEval (c : PresentationCode) (edges : List (Raw × Raw)) :
    FreeGroup (Fin edges.length) →* Carrier c :=
  FreeGroup.lift fun i => PresentedGroup.mk (codeRels c) (targetWord c edges i)

@[simp] theorem sourceEval_of (c : PresentationCode)
    (edges : List (Raw × Raw)) (i : Fin edges.length) :
    sourceEval c edges (FreeGroup.of i) =
      PresentedGroup.mk (codeRels c) (sourceWord c edges i) := by
  simp [sourceEval]

@[simp] theorem targetEval_of (c : PresentationCode)
    (edges : List (Raw × Raw)) (i : Fin edges.length) :
    targetEval c edges (FreeGroup.of i) =
      PresentedGroup.mk (codeRels c) (targetWord c edges i) := by
  simp [targetEval]

/-- The honest free-edge data.  These two injectivity arguments are precisely
the semantic freeness obligations left by the raw compiler. -/
def edgeData (c : PresentationCode) (edges : List (Raw × Raw))
    (hsource : Function.Injective (sourceEval c edges))
    (htarget : Function.Injective (targetEval c edges)) :
    Data (Fin edges.length) (Carrier c) where
  source := sourceEval c edges
  target := targetEval c edges
  source_injective := hsource
  target_injective := htarget

/-- The explicitly embedded source free group is exactly the subgroup used by
the word-level HNN presentation. -/
theorem sourceSubgroup_edgeData (c : PresentationCode)
    (edges : List (Raw × Raw))
    (hsource : Function.Injective (sourceEval c edges))
    (htarget : Function.Injective (targetEval c edges)) :
    sourceSubgroup (edgeData c edges hsource htarget) =
      HNNPresentation.srcSub (codeRels c) (sourceWord c edges) := by
  rw [sourceSubgroup, HNNPresentation.srcSub,
    ← FreeGroup.closure_range_of, MonoidHom.map_closure]
  congr 1
  ext x
  simp [edgeData, HNNPresentation.srcGen]

/-- The explicitly embedded target free group is exactly the subgroup used by
the word-level HNN presentation. -/
theorem targetSubgroup_edgeData (c : PresentationCode)
    (edges : List (Raw × Raw))
    (hsource : Function.Injective (sourceEval c edges))
    (htarget : Function.Injective (targetEval c edges)) :
    targetSubgroup (edgeData c edges hsource htarget) =
      HNNPresentation.tgtSub (codeRels c) (targetWord c edges) := by
  rw [targetSubgroup, HNNPresentation.tgtSub,
    ← FreeGroup.closure_range_of, MonoidHom.map_closure]
  congr 1
  ext x
  simp [edgeData, HNNPresentation.tgtGen]

end FreeEdgeTowerSemantics
end GroupApproximation
