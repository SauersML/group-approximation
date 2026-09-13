import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The edges with one face on both sides of a planar map form a forest

Osin (math/0411039v3, §9), proof of Lemma 9.4, (38): "`k_i ≤ 4 n_i`".  The cutting paths of a
component polygon run along edges with the polygon's own face on both sides.  In a planar map these
edges form a forest, so once there is one of them there are fewer of them than vertices they meet.
This is the one planarity input of the count of cutting sides (`OsinLemma94CuttingSidesStatement`).

* `CombMap.sameFaceDarts`, `CombMap.sameFaceVertices`: the darts with the face `f` on both sides,
  and the vertices they start at.
* `SameFaceDartForestStatement`: in a planar map, once there is such a dart,
  `#darts + 2 ≤ 2 · #vertices`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, "Hull's small cancellation theorem",
through Osin's Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

namespace CombMap

/-- The darts with the face `f` on both sides. -/
noncomputable def sameFaceDarts (M : CombMap.{u}) (f : M.Face) : Finset M.Dart := by
  classical
  exact Finset.univ.filter fun d => M.faceOf d = f ∧ M.faceOf (M.alpha d) = f

theorem mem_sameFaceDarts (M : CombMap.{u}) (f : M.Face) (d : M.Dart) :
    d ∈ M.sameFaceDarts f ↔ M.faceOf d = f ∧ M.faceOf (M.alpha d) = f := by
  classical
  unfold sameFaceDarts
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ d, h⟩⟩

/-- The vertices at which the darts with the face `f` on both sides start. -/
noncomputable def sameFaceVertices (M : CombMap.{u}) (f : M.Face) : Finset M.Vertex := by
  classical
  exact (M.sameFaceDarts f).image M.vertexOf

end CombMap

/-- **The edges with one face on both sides form a forest.**  In a planar map, the darts with
the face `f` on both sides are the darts of the edges with `f` on both sides.  These edges contain
no cycle, so, once there is one of them, there are fewer of them than vertices they meet:
`#darts + 2 ≤ 2 · #vertices`. -/
def SameFaceDartForestStatement : Prop :=
  ∀ (M : CombMap.{u}), M.IsPlanar → ∀ f : M.Face, (M.sameFaceDarts f).Nonempty →
    (M.sameFaceDarts f).card + 2 ≤ 2 * (M.sameFaceVertices f).card

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.mem_sameFaceDarts
