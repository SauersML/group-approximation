import GroupApproximation.Computability.BenignInfCode
import GroupApproximation.Computability.BenignSupCode

/-!
# Effective witness syntax for an agreement operation

The subgroup identity used for Higman's `ζ` and `π` operations is

    ((A_B ⊔ R_V) ⊓ ker(retK)) ⊓ A_E.

This file implements that identity literally on finite witness syntax: one
join followed by two intersections.  The four inputs are the witness for
`A_B` and the three fixed witnesses for `R_V`, `ker(retK)`, and `A_E`.
No presentation or marked word is chosen inside the transform.
-/

namespace GroupApproximation
namespace Higman
namespace ReifiedHigmanWitnessAgreeCode

abbrev WitnessSyntax := BenignInfCode.WitnessSyntax

/-- Input order: the varying witness, row witness, return-kernel witness, and
all-sequences witness. -/
abbrev Input := WitnessSyntax × (WitnessSyntax × (WitnessSyntax × WitnessSyntax))

def varying (x : Input) : WitnessSyntax := x.1
def row (x : Input) : WitnessSyntax := x.2.1
def returnKernel (x : Input) : WitnessSyntax := x.2.2.1
def allSequences (x : Input) : WitnessSyntax := x.2.2.2

def joined (x : Input) : WitnessSyntax :=
  BenignSupCode.transform (varying x, row x)

def cutToKernel (x : Input) : WitnessSyntax :=
  BenignInfCode.transform (joined x, returnKernel x)

/-- **The literal `⊔/⊓/⊓` agreement-witness compiler.** -/
def transform (x : Input) : WitnessSyntax :=
  BenignInfCode.transform (cutToKernel x, allSequences x)

@[simp] theorem transform_code (x : Input) :
    (transform x).1 =
      DirectProductCode.productCode (cutToKernel x).1 (allSequences x).1 := rfl

theorem primrec_varying : Primrec varying := Primrec.fst
theorem primrec_row : Primrec row := Primrec.fst.comp Primrec.snd
theorem primrec_returnKernel : Primrec returnKernel :=
  (Primrec.fst.comp Primrec.snd).comp Primrec.snd
theorem primrec_allSequences : Primrec allSequences :=
  (Primrec.snd.comp Primrec.snd).comp Primrec.snd

theorem primrec_joined : Primrec joined :=
  BenignSupCode.primrec_transform.comp
    (Primrec.pair primrec_varying primrec_row)

theorem primrec_cutToKernel : Primrec cutToKernel :=
  BenignInfCode.primrec_transform.comp
    (Primrec.pair primrec_joined primrec_returnKernel)

theorem primrec_transform : Primrec transform :=
  BenignInfCode.primrec_transform.comp
    (Primrec.pair primrec_cutToKernel primrec_allSequences)

theorem computable_transform : Computable transform :=
  primrec_transform.to_comp

end ReifiedHigmanWitnessAgreeCode
end Higman
end GroupApproximation
