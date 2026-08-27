import GroupApproximation.Manuscript.MFRecognition.MarkedHigmanRopeInput
import GroupApproximation.Manuscript.MFRecognition.RopeObjectsProfinite

/-!
# The marked Higman output as a profinite rope input

This is the direct adapter from the finite marked presentation emitted by the
Higman compiler and the bridge map used by the manuscript to the concrete
profinite rope witness.  It contains no generic benign join or amalgamated
`mapEmb` transport.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace MarkedHigmanOutput

noncomputable section

variable {P : RecPresCode} (o : MarkedHigmanOutput P)

/-- The marked output and bridge data therefore produce the literal
four-field witness consumed by the first rope. -/
def ropeProfiniteWitness
    {Qplus : Type} [Group Qplus]
    (qplus : Source →* Qplus)
    (j : Qplus →* Rope.Ptarget) (hj : Function.Injective j)
    (hN : kernelN P ≤ qplus.ker)
    [Group.ResiduallyFinite (Host o.host)] :
    Higman.ProfiniteBenignWitness (kernelN P) :=
  by
    -- The rope input's host is the marked output's host, but only after
    -- `ropeInput` is unfolded; instance search does not unfold a plain `def`,
    -- so the ambient hypothesis is transported by hand.
    letI : Group.ResiduallyFinite
        (FreeGroup (o.ropeInput qplus j hj hN).X ⧸
          Subgroup.normalClosure (o.ropeInput qplus j hj hN).R) :=
      inferInstanceAs (Group.ResiduallyFinite (Host o.host))
    simpa only [ropeInput] using
      (Rope.RopeInput.profiniteWitness (o.ropeInput qplus j hj hN))

/-- The exact central rope assembled from a marked output and the bridge is
residually finite on the RF-host positive branch. -/
theorem centralRope_residuallyFinite
    {Qplus : Type} [Group Qplus]
    (qplus : Source →* Qplus)
    (j : Qplus →* Rope.Ptarget) (hj : Function.Injective j)
    (hN : kernelN P ≤ qplus.ker)
    [Group.ResiduallyFinite (Host o.host)] :
    Group.ResiduallyFinite
      (Rope.RopeInput.CentralRope (o.ropeInput qplus j hj hN)) :=
  by
    letI : Group.ResiduallyFinite
        (FreeGroup (o.ropeInput qplus j hj hN).X ⧸
          Subgroup.normalClosure (o.ropeInput qplus j hj hN).R) :=
      inferInstanceAs (Group.ResiduallyFinite (Host o.host))
    simpa only [ropeInput] using
      (Rope.RopeInput.centralRope_residuallyFinite
        (o.ropeInput qplus j hj hN))

end

end MarkedHigmanOutput
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
