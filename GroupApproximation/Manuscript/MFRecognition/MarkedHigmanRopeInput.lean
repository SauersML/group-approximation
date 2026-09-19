import GroupApproximation.Manuscript.MFRecognition.MarkedHigmanOutput
import GroupApproximation.Manuscript.MFRecognition.RopeObjects

/-!
# Marked Higman output to the concrete rope input

This adapter uses only the proved marked-output semantics and the bridge
data.  In particular it does not import the old `EffectiveHigmanCompiler`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace MarkedHigmanOutput

noncomputable section

variable {P : RecPresCode} (o : MarkedHigmanOutput P)

/-- Assemble the manuscript's literal `RopeInput` from a marked Higman output
and the bridge map. -/
def ropeInput
    {Qplus : Type} [Group Qplus]
    (qplus : Source →* Qplus)
    (j : Qplus →* Rope.Ptarget) (hj : Function.Injective j)
    (hN : kernelN P ≤ qplus.ker) : Rope.RopeInput where
  X := HostAlphabet o.host
  R := hostRelators o.host
  Rfinite := hostRelators_finite o.host
  words := o.markedWord
  Qplus := Qplus
  qplus := qplus
  j := j
  j_injective := hj
  N := kernelN P
  Nnormal := Subgroup.normalClosure_normal
  mem_L0_iff := fun f ↦
    (Higman.MikhailovaRankThree.input_mem_cutting_iff
      (hostRelators o.host) o.markedWord f).trans
      (o.hostQuotient_markedWord_eq_one_iff f)
  N_le_Nplus := hN

end


end MarkedHigmanOutput
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
