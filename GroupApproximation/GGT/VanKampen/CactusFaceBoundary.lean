import GroupApproximation.GGT.VanKampen.CactusBoundary

/-!
# Based face boundaries of the polygon cactus

The face classifier of `CactusTopology` supplies one explicit dart in the
outer face, in every relator face, and in the complementary face.  This file
bases the ordered orbit enumeration of `CactusBoundary` at those darts and
transports it to every face through the classifier equivalence.  The three
named face constructors are pairwise distinct, and evaluating the global
boundary choice on a named face returns the corresponding based orbit list.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

namespace CactusShape

noncomputable local instance cactusDartDecidableEq (S : CactusShape) :
    DecidableEq S.toCombMap.Dart :=
  Classical.decEq _

/-- The actual face represented by an explicit cactus face index. -/
def indexedFace (S : CactusShape) (i : S.FaceIndex) : S.toCombMap.Face :=
  S.toCombMap.faceOf (S.faceRepresentative i)

/-- The face classifier sends the face represented by `i` back to `i`. -/
theorem faceEquiv_indexedFace (S : CactusShape) (i : S.FaceIndex) :
    S.faceEquiv (S.indexedFace i) = i := by
  exact S.faceClass_representative i

/-- Every face is the explicitly represented face selected by its index. -/
theorem indexedFace_faceEquiv (S : CactusShape) (f : S.toCombMap.Face) :
    S.indexedFace (S.faceEquiv f) = f := by
  apply S.faceEquiv.injective
  exact S.faceEquiv_indexedFace (S.faceEquiv f)

/-- The outer polygon face. -/
def outerFace (S : CactusShape) : S.toCombMap.Face :=
  S.indexedFace .outer

/-- The forward face of the `i`-th relator polygon. -/
def relatorFace (S : CactusShape) (i : Fin S.cellCount) :
    S.toCombMap.Face :=
  S.indexedFace (.relator i)

/-- The complementary face containing all stems. -/
def bigFace (S : CactusShape) : S.toCombMap.Face :=
  S.indexedFace .big

theorem relatorFace_ne_outerFace (S : CactusShape)
    (i : Fin S.cellCount) : S.relatorFace i ≠ S.outerFace := by
  intro h
  have hi := congrArg S.faceEquiv h
  simp [relatorFace, outerFace, S.faceEquiv_indexedFace] at hi

theorem bigFace_ne_outerFace (S : CactusShape) :
    S.bigFace ≠ S.outerFace := by
  intro h
  have hi := congrArg S.faceEquiv h
  simp [bigFace, outerFace, S.faceEquiv_indexedFace] at hi

theorem relatorFace_injective (S : CactusShape) :
    Function.Injective S.relatorFace := by
  intro i j h
  have hi := congrArg S.faceEquiv h
  simpa [relatorFace, S.faceEquiv_indexedFace] using hi

theorem bigFace_ne_relatorFace (S : CactusShape)
    (i : Fin S.cellCount) : S.bigFace ≠ S.relatorFace i := by
  intro h
  have hi := congrArg S.faceEquiv h
  simp [bigFace, relatorFace, S.faceEquiv_indexedFace] at hi

/-- The ordered face boundary based at the representative of an index. -/
noncomputable def indexedFaceBoundary (S : CactusShape) (i : S.FaceIndex) :
    FaceBoundary S.toCombMap (S.indexedFace i) :=
  FaceBoundary.based S.toCombMap (S.faceRepresentative i)

/-- A coherent based boundary choice for every cactus face. -/
noncomputable def faceBoundary (S : CactusShape)
    (f : S.toCombMap.Face) : FaceBoundary S.toCombMap f :=
  S.indexedFace_faceEquiv f ▸ S.indexedFaceBoundary (S.faceEquiv f)

/-- Transporting a face boundary does not change its dart list. -/
theorem faceBoundary_darts_transport {M : CombMap.{0}} {f g : M.Face}
    (h : f = g) (B : FaceBoundary M f) : (h ▸ B).darts = B.darts := by
  cases h
  rfl

/-- At an explicitly indexed face, the global choice has the canonical based
dart list. -/
theorem faceBoundary_indexedFace_darts (S : CactusShape) (i : S.FaceIndex) :
    (S.faceBoundary (S.indexedFace i)).darts =
      (S.indexedFaceBoundary i).darts := by
  rw [faceBoundary]
  calc
    (S.indexedFace_faceEquiv (S.indexedFace i) ▸
          S.indexedFaceBoundary (S.faceEquiv (S.indexedFace i))).darts =
        (S.indexedFaceBoundary (S.faceEquiv (S.indexedFace i))).darts :=
      faceBoundary_darts_transport _ _
    _ = (S.indexedFaceBoundary i).darts := by
      rw [S.faceEquiv_indexedFace]

/-- The global outer boundary starts at the distinguished forward dart. -/
theorem faceBoundary_outerFace_darts (S : CactusShape) :
    (S.faceBoundary S.outerFace).darts =
      (S.indexedFaceBoundary .outer).darts := by
  exact S.faceBoundary_indexedFace_darts .outer

/-- The global boundary of a relator face starts at its distinguished forward
dart. -/
theorem faceBoundary_relatorFace_darts (S : CactusShape)
    (i : Fin S.cellCount) :
    (S.faceBoundary (S.relatorFace i)).darts =
      (S.indexedFaceBoundary (.relator i)).darts := by
  exact S.faceBoundary_indexedFace_darts (.relator i)

/-- The global complementary boundary starts at the distinguished backward
outer dart. -/
theorem faceBoundary_bigFace_darts (S : CactusShape) :
    (S.faceBoundary S.bigFace).darts =
      (S.indexedFaceBoundary .big).darts := by
  exact S.faceBoundary_indexedFace_darts .big

end CactusShape

end VanKampen
end GGT
end GroupApproximation
