import GroupApproximation.Higman.ReifiedHigmanWitnessBaseCode
import GroupApproximation.Computability.BenignComapCode

/-!
# The effective final stage of Higman's theta operation

At subgroup level, `A_(θ B)` is the preimage of the even-coordinate witness
under the injective endomorphism

    a ↦ a,  b ↦ b,  c ↦ c².

This file implements that comap on finite witness syntax.  Its input is the
coded witness for the preceding `evenOp B` stage; no hypothesis or semantic
structure is hidden in the transform.  The source factor is the literal free
rank-three code, and the right marks spell `a,b,c²` directly.
-/

namespace GroupApproximation
namespace Higman
namespace ReifiedHigmanWitnessThetaCode

open ReifiedPrimrecTower ReifiedHigmanWitnessBaseCode

abbrev Raw := BenignInfCode.Raw
abbrev WitnessSyntax := BenignInfCode.WitnessSyntax

def markAt (x : WitnessSyntax) (i : ℕ) : Raw := x.2.2.getD i []

/-- The right-factor images of the six canonical source marks under
`a ↦ a, b ↦ b, c ↦ c²`. -/
def doubledMarks (x : WitnessSyntax) : List Raw :=
  [markAt x 0, markAt x 1, markAt x 2 ++ markAt x 2, [], [], []]

/-- The free rank-three overgroup syntax supplying the left factor of the
effective preimage construction. -/
def sourceOvergroupSyntax : WitnessSyntax :=
  (rankThreeBaseCode, ([], sourceSixMarks))

def rightSyntax (x : WitnessSyntax) : WitnessSyntax :=
  (x.1, (x.2.1, doubledMarks x))

def comapInput (x : WitnessSyntax) : BenignComapCode.Input :=
  (sourceOvergroupSyntax, rightSyntax x)

/-- **Concrete final code transform for `θ`.** -/
def transform (x : WitnessSyntax) : WitnessSyntax :=
  BenignComapCode.transform (comapInput x)

@[simp] theorem transform_code (x : WitnessSyntax) :
    (transform x).1 = BenignSupCode.productBase (comapInput x) := rfl

@[simp] theorem transform_cutting (x : WitnessSyntax) :
    (transform x).2.1 =
      BenignSupCode.leftGeneratorWords (comapInput x) ++
        BenignInfCode.rightCuttingWords (comapInput x) := rfl

theorem primrec_markAt (i : ℕ) :
    Primrec (fun x : WitnessSyntax => markAt x i) :=
  (Primrec.list_getD []).comp (Primrec.snd.comp Primrec.snd)
    (Primrec.const i)

theorem primrec_doubledMark :
    Primrec (fun x : WitnessSyntax => markAt x 2 ++ markAt x 2) :=
  Primrec.list_append.comp (primrec_markAt 2) (primrec_markAt 2)

theorem primrec_doubledMarks : Primrec doubledMarks :=
  Primrec.list_cons.comp (primrec_markAt 0)
    (Primrec.list_cons.comp (primrec_markAt 1)
      (Primrec.list_cons.comp primrec_doubledMark
        (Primrec.list_cons.comp (Primrec.const [])
          (Primrec.list_cons.comp (Primrec.const [])
            (Primrec.list_cons.comp (Primrec.const [])
              (Primrec.const []))))))

theorem primrec_sourceOvergroupSyntax :
    Primrec (fun _ : Unit => sourceOvergroupSyntax) := Primrec.const _

theorem primrec_rightSyntax : Primrec rightSyntax :=
  Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd) primrec_doubledMarks)

theorem primrec_comapInput : Primrec comapInput :=
  Primrec.pair (Primrec.const sourceOvergroupSyntax) primrec_rightSyntax

theorem primrec_transform : Primrec transform :=
  BenignComapCode.primrec_transform.comp primrec_comapInput

theorem computable_transform : Computable transform :=
  primrec_transform.to_comp

end ReifiedHigmanWitnessThetaCode
end Higman
end GroupApproximation
