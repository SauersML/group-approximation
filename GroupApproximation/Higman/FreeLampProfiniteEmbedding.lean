import GroupApproximation.Higman.FreeLampFinitePresentation
import GroupApproximation.Higman.ProfiniteBenignWitness

/-!
# The canonical vertex of a free lamp is profinitely embedded

The free-lamp amalgam `G *_L (L × K)` retracts onto `G` by killing the lamp
factor.  Consequently its canonical copy of `G` is both profinitely closed
and carries the full induced profinite topology.  This is the embedding field
needed by the paired-return benign witness.
-/

namespace GroupApproximation
namespace Higman
namespace FreeLampProfiniteEmbedding

noncomputable section

open Monoid
open FreeLampFinitePresentation

variable (G : Type) [Group G] (L : Subgroup G)
variable (K : Type) [Group K]

/-- Factor maps which forget the free lamp coordinate. -/
def baseRetFactors : ∀ b, LampFactor G L K b →* G
  | true => MonoidHom.id G
  | false => L.subtype.comp (MonoidHom.fst L K)

theorem baseRetFactors_comp : ∀ b,
    (baseRetFactors G L K b).comp (lampMap G L K b) = L.subtype := by
  intro b
  cases b <;> rfl

/-- Kill the lamp group and retain the ambient vertex. -/
def baseRet : FreeLamp G L K →* G :=
  PushoutI.lift (baseRetFactors G L K) L.subtype
    (baseRetFactors_comp G L K)

@[simp] theorem baseRet_inAmbient (g : G) :
    baseRet G L K (inAmbient G L K g) = g := by
  exact PushoutI.lift_of _ _ _ _

theorem baseRet_comp_inAmbient :
    (baseRet G L K).comp (inAmbient G L K) = MonoidHom.id G := by
  apply MonoidHom.ext
  exact baseRet_inAmbient G L K

/-- The canonical vertex embedding carries cofinally all finite quotients of
the vertex group. -/
theorem inAmbient_cofinal :
    CofinalProfiniteEmbedding (inAmbient G L K) :=
  CofinalProfiniteEmbedding.postcomp_of_retraction
    CofinalProfiniteEmbedding.id (inAmbient G L K) (baseRet G L K)
    (baseRet_comp_inAmbient G L K)

/-- In a residually finite free lamp, its canonical vertex is profinitely
closed. -/
theorem profiniteClosure_inAmbient [Group.ResiduallyFinite (FreeLamp G L K)] :
    profiniteClosure (inAmbient G L K).range = (inAmbient G L K).range :=
  profiniteClosure_range_eq_range_of_retraction
    (inAmbient G L K) (baseRet G L K) (baseRet_comp_inAmbient G L K)

end

end FreeLampProfiniteEmbedding
end Higman
end GroupApproximation
