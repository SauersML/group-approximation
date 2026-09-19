import GroupApproximation.Higman.CodedBenignWitness
import GroupApproximation.Higman.ReifiedHigmanWitnessAgreeCode
import GroupApproximation.Higman.CurrentOperationClosures

/-!
# Fixed coded witnesses for Higman's agreement operations

The row witnesses used by `ζ` and `π`, and the return-kernel witness, are
closed theorems.  We encode those witnesses once as finite presentation data.
The witness for all coded sequences is precisely the remaining semantic
`OmegaInput` dependency, so it is encoded from that input rather than hidden
in a new interface.
-/

namespace GroupApproximation
namespace Higman
namespace ReifiedHigmanWitnessAgreeConstants

noncomputable section

open ReifiedHigmanWitnessAgreeCode
open Conj

abbrev WitnessSyntax := BenignInfCode.WitnessSyntax
abbrev MarkCount := CodedBenignWitness.MarkCount

/-- The six-mark convention used by the reified calculus: `a,b,c,1,1,1`. -/
def canonicalMarks : List F₃ := [a, b, c, 1, 1, 1]

def canonicalMark (i : MarkCount) : F₃ :=
  canonicalMarks.getD i 1

noncomputable def modelOf {H : Subgroup F₃} (h : BenignTF H) :
    CodedBenignWitness.Model canonicalMark H :=
  CodedBenignWitness.model canonicalMark (Classical.choice h).witness

/-- Fixed finite syntax for the row subgroup used by `ζ`. -/
noncomputable def zetaRowModel :
    CodedBenignWitness.Model canonicalMark (Agree.rowSub Agree.zetaV) :=
  modelOf RowDeletionGraph.zeta_row_benignTF

/-- Fixed finite syntax for the positive row subgroup used by `π`. -/
noncomputable def piRowModel :
    CodedBenignWitness.Model canonicalMark (Agree.rowSub Agree.piV) :=
  modelOf benignTF_rowSub_piV

/-- Fixed finite syntax for the kernel of the coordinate return map. -/
noncomputable def returnKernelModel :
    CodedBenignWitness.Model canonicalMark (MonoidHom.ker Coord.retK) :=
  modelOf Coord.benignTF_ker_retK

/-- Finite syntax for all coded sequences, obtained from the one remaining
semantic operation-closure input. -/
noncomputable def allSequencesModel (k : Omega.OmegaInput) :
    CodedBenignWitness.Model canonicalMark (Seq.ASub (Set.univ : Set Seq.E)) :=
  modelOf (Omega.benignTF_ASub_univ k)

noncomputable def zetaInput (k : Omega.OmegaInput) (x : WitnessSyntax) :
    ReifiedHigmanWitnessAgreeCode.Input :=
  (x, (zetaRowModel.coded,
    (returnKernelModel.coded, (allSequencesModel k).coded)))

noncomputable def piInput (k : Omega.OmegaInput) (x : WitnessSyntax) :
    ReifiedHigmanWitnessAgreeCode.Input :=
  (x, (piRowModel.coded,
    (returnKernelModel.coded, (allSequencesModel k).coded)))

/-- **Concrete finite-syntax compiler for `ζ`, conditional only on the actual
remaining `OmegaInput` theorem.** -/
noncomputable def zetaTransform (k : Omega.OmegaInput) (x : WitnessSyntax) :
    WitnessSyntax :=
  ReifiedHigmanWitnessAgreeCode.transform (zetaInput k x)

/-- **Concrete finite-syntax compiler for `π`, conditional only on the actual
remaining `OmegaInput` theorem.** -/
noncomputable def piTransform (k : Omega.OmegaInput) (x : WitnessSyntax) :
    WitnessSyntax :=
  ReifiedHigmanWitnessAgreeCode.transform (piInput k x)

theorem primrec_zetaInput (k : Omega.OmegaInput) : Primrec (zetaInput k) :=
  Primrec.pair Primrec.id
    (Primrec.pair (Primrec.const zetaRowModel.coded)
      (Primrec.pair (Primrec.const returnKernelModel.coded)
        (Primrec.const (allSequencesModel k).coded)))

theorem primrec_piInput (k : Omega.OmegaInput) : Primrec (piInput k) :=
  Primrec.pair Primrec.id
    (Primrec.pair (Primrec.const piRowModel.coded)
      (Primrec.pair (Primrec.const returnKernelModel.coded)
        (Primrec.const (allSequencesModel k).coded)))

theorem primrec_zetaTransform (k : Omega.OmegaInput) :
    Primrec (zetaTransform k) :=
  ReifiedHigmanWitnessAgreeCode.primrec_transform.comp (primrec_zetaInput k)

theorem primrec_piTransform (k : Omega.OmegaInput) :
    Primrec (piTransform k) :=
  ReifiedHigmanWitnessAgreeCode.primrec_transform.comp (primrec_piInput k)

theorem computable_zetaTransform (k : Omega.OmegaInput) :
    Computable (zetaTransform k) :=
  (primrec_zetaTransform k).to_comp

theorem computable_piTransform (k : Omega.OmegaInput) :
    Computable (piTransform k) :=
  (primrec_piTransform k).to_comp

end


end ReifiedHigmanWitnessAgreeConstants
end Higman
end GroupApproximation
