import GroupApproximation.Computability.BenignInfCode
import GroupApproximation.Higman.MikhailovaRopeCode

/-!
# Effective syntax for the two-HNN benign join construction

This is the code-level form of `Higman.joinWitness`: form the product base,
centralize `L₁ × ⊤`, then centralize `⊤ × L₂`, and cut with the two
stable conjugates of the six diagonal source marks.
-/

namespace GroupApproximation
namespace BenignSupCode

open PresentationCodes DirectProductCode FreeEdgeTowerCode
open Higman.MikhailovaRopeCode

abbrev Raw : Type := BenignInfCode.Raw
abbrev Input : Type := BenignInfCode.Input
abbrev Output : Type := BenignInfCode.WitnessSyntax

def generatorWords (c : PresentationCode) : List Raw :=
  (List.range (genCount c)).map fun i => [(i, true)]

def productBase (x : Input) : PresentationCode :=
  productCode (BenignInfCode.leftCode x) (BenignInfCode.rightCode x)

def m1Words (x : Input) : List Raw :=
  BenignInfCode.leftCuttingWords x ++
    (generatorWords (BenignInfCode.rightCode x)).map
      (rightWord (BenignInfCode.leftCode x) (BenignInfCode.rightCode x))

def m2Words (x : Input) : List Raw :=
  (generatorWords (BenignInfCode.leftCode x)).map
      (leftWord (BenignInfCode.leftCode x)) ++
    BenignInfCode.rightCuttingWords x

def level1 (x : Input) : PresentationCode :=
  firstStageCode (productBase x) (m1Words x)

def level2 (x : Input) : PresentationCode :=
  firstStageCode (level1 x) (m2Words x)

def firstConjugates (x : Input) : List Raw :=
  (BenignInfCode.diagonalMarks x).map
    (firstStableConjugate (productBase x))

def secondConjugates (x : Input) : List Raw :=
  (BenignInfCode.diagonalMarks x).map
    (firstStableConjugate (level1 x))

/-- The complete six-mark join-witness syntax. -/
def transform (x : Input) : Output :=
  (level2 x,
    (firstConjugates x ++ secondConjugates x,
      BenignInfCode.diagonalMarks x))

@[simp] theorem transform_code (x : Input) : (transform x).1 = level2 x := rfl

@[simp] theorem transform_cutting (x : Input) :
    (transform x).2.1 = firstConjugates x ++ secondConjugates x := rfl

@[simp] theorem transform_marks (x : Input) :
    (transform x).2.2 = BenignInfCode.diagonalMarks x := rfl

theorem primrec_generatorWord :
    Primrec (fun i : ℕ => ([(i, true)] : Raw)) :=
  Primrec.list_cons.comp (Primrec.pair Primrec.id (Primrec.const true))
    (Primrec.const [])

theorem primrec_generatorWords : Primrec generatorWords :=
  Primrec.list_map
    (Primrec.list_range.comp PresentationCodes.primrec_genCount)
    (primrec_generatorWord.comp Primrec.snd)

theorem primrec_productBase : Primrec productBase :=
  primrec_productCode.comp
    (Primrec.pair BenignInfCode.primrec_leftCode
      BenignInfCode.primrec_rightCode)

def rightGeneratorWordInput (a : Input × Raw) :
    (PresentationCode × PresentationCode) × Raw :=
  ((BenignInfCode.leftCode a.1, BenignInfCode.rightCode a.1), a.2)

theorem primrec_rightGeneratorWordInput : Primrec rightGeneratorWordInput :=
  Primrec.pair
    (Primrec.pair
      (BenignInfCode.primrec_leftCode.comp Primrec.fst)
      (BenignInfCode.primrec_rightCode.comp Primrec.fst)) Primrec.snd

def rightGeneratorWord (a : Input × Raw) : Raw :=
  rightWord (rightGeneratorWordInput a).1.1 (rightGeneratorWordInput a).1.2
    (rightGeneratorWordInput a).2

theorem primrec_rightGeneratorWord : Primrec rightGeneratorWord :=
  primrec_rightWord.comp primrec_rightGeneratorWordInput

theorem primrec_rightGeneratorWords : Primrec (fun x : Input =>
    (generatorWords (BenignInfCode.rightCode x)).map fun w =>
      rightGeneratorWord (x, w)) :=
  Primrec.list_map
    (primrec_generatorWords.comp BenignInfCode.primrec_rightCode)
    primrec_rightGeneratorWord

theorem primrec_m1Words : Primrec m1Words :=
  Primrec.list_append.comp BenignInfCode.primrec_leftCuttingWords
    primrec_rightGeneratorWords

theorem primrec_leftGeneratorWord : Primrec
    (fun a : Input × Raw =>
      leftWord (BenignInfCode.leftCode a.1) a.2) :=
  Primrec₂.comp primrec_leftWord
    (BenignInfCode.primrec_leftCode.comp Primrec.fst) Primrec.snd

theorem primrec_leftGeneratorWords : Primrec (fun x : Input =>
    (generatorWords (BenignInfCode.leftCode x)).map fun w =>
      leftWord (BenignInfCode.leftCode x) w) :=
  Primrec.list_map
    (primrec_generatorWords.comp BenignInfCode.primrec_leftCode)
    primrec_leftGeneratorWord

theorem primrec_m2Words : Primrec m2Words :=
  Primrec.list_append.comp primrec_leftGeneratorWords
    BenignInfCode.primrec_rightCuttingWords

theorem primrec_level1 : Primrec level1 :=
  primrec_firstStageCode.comp (Primrec.pair primrec_productBase primrec_m1Words)

theorem primrec_level2 : Primrec level2 :=
  primrec_firstStageCode.comp (Primrec.pair primrec_level1 primrec_m2Words)

def firstConjugateInput (a : Input × Raw) : PresentationCode × Raw :=
  (productBase a.1, a.2)

theorem primrec_firstConjugateInput : Primrec firstConjugateInput :=
  Primrec.pair (primrec_productBase.comp Primrec.fst) Primrec.snd

theorem primrec_firstConjugates : Primrec firstConjugates :=
  Primrec.list_map BenignInfCode.primrec_diagonalMarks
    (primrec_firstStableConjugate.comp primrec_firstConjugateInput)

def secondConjugateInput (a : Input × Raw) : PresentationCode × Raw :=
  (level1 a.1, a.2)

theorem primrec_secondConjugateInput : Primrec secondConjugateInput :=
  Primrec.pair (primrec_level1.comp Primrec.fst) Primrec.snd

theorem primrec_secondConjugates : Primrec secondConjugates :=
  Primrec.list_map BenignInfCode.primrec_diagonalMarks
    (primrec_firstStableConjugate.comp primrec_secondConjugateInput)

theorem primrec_transform : Primrec transform :=
  Primrec.pair primrec_level2
    (Primrec.pair
      (Primrec.list_append.comp primrec_firstConjugates primrec_secondConjugates)
      BenignInfCode.primrec_diagonalMarks)

theorem computable_transform : Computable transform :=
  primrec_transform.to_comp

end BenignSupCode
end GroupApproximation
