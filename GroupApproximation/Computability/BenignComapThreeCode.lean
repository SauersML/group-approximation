import GroupApproximation.Computability.BenignComapCode

/-! Three-mark specialization of the benign preimage syntax transform. -/

namespace GroupApproximation
namespace BenignComapThreeCode

abbrev Input : Type := BenignInfCode.Input
abbrev Output : Type := BenignInfCode.WitnessSyntax

def diagonalMarks (x : Input) : List BenignInfCode.Raw :=
  [BenignInfCode.diagonalAt x 0, BenignInfCode.diagonalAt x 1,
    BenignInfCode.diagonalAt x 2]

def transform (x : Input) : Output :=
  (BenignSupCode.productBase x,
    (BenignSupCode.leftGeneratorWords x ++
      BenignInfCode.rightCuttingWords x, diagonalMarks x))

theorem primrec_diagonalMarks : Primrec diagonalMarks :=
  Primrec.list_cons.comp (BenignInfCode.primrec_diagonalAt 0)
    (Primrec.list_cons.comp (BenignInfCode.primrec_diagonalAt 1)
      (Primrec.list_cons.comp (BenignInfCode.primrec_diagonalAt 2)
        (Primrec.const [])))

theorem primrec_transform : Primrec transform :=
  Primrec.pair BenignSupCode.primrec_productBase
    (Primrec.pair
      (Primrec.list_append.comp BenignSupCode.primrec_leftGeneratorWords
        BenignInfCode.primrec_rightCuttingWords)
      primrec_diagonalMarks)

theorem computable_transform : Computable transform :=
  primrec_transform.to_comp

end BenignComapThreeCode
end GroupApproximation
