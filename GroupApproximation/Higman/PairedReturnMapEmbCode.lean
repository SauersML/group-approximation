import GroupApproximation.Higman.PairedReturnCutterCode
import GroupApproximation.Computability.BenignMapEmbRopeInput

/-!
# Effective mapEmb step from the fixed paired-return leaf

The paired-return witness is fixed.  A varying target therefore supplies only
its presentation code, six raw words spelling the images of the canonical
`F₃ × F₃` generators, and the three marked words ultimately consumed by
the rope compiler.  This file pairs those six words with the fixed ambient
representatives, transports the fixed cutter through `BenignMapEmbCode`, and
immediately emits both `RankThreeInputData` and the compiled presentation.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnMapEmbCode

open PresentationCodes
open PairedReturnCutterCode
open BenignMapEmbCode BenignMapEmbRopeInput
open MikhailovaRopeCode

abbrev Raw : Type := List (ℕ × Bool)

/-- Varying target code, the six images of `P`'s canonical generators, and
the three final marked words. -/
abbrev Input : Type := PresentationCode × (List Raw × RankThreeWords)

def targetGeneratorWord (x : Input) (i : ℕ) : Raw :=
  x.2.1.getD i []

noncomputable def fixedAmbientGeneratorWord (i : ℕ) : Raw :=
  ambientPGeneratorWords.getD i []

/-- The six displayed gluing pairs, in the canonical order of `pGenerators`. -/
noncomputable def edgePairs (x : Input) : List (Raw × Raw) :=
  [(fixedAmbientGeneratorWord 0, targetGeneratorWord x 0),
    (fixedAmbientGeneratorWord 1, targetGeneratorWord x 1),
    (fixedAmbientGeneratorWord 2, targetGeneratorWord x 2),
    (fixedAmbientGeneratorWord 3, targetGeneratorWord x 3),
    (fixedAmbientGeneratorWord 4, targetGeneratorWord x 4),
    (fixedAmbientGeneratorWord 5, targetGeneratorWord x 5)]

def threeMarkedWords (x : Input) : List Raw :=
  [x.2.2.1, x.2.2.2.1, x.2.2.2.2]

/-- The concrete input to the generic effective `mapEmb` transform. -/
noncomputable def mapEmbInput (x : Input) : BenignMapEmbCode.Input :=
  (((ambientCode, x.1), edgePairs x), (fiveWords, threeMarkedWords x))

/-- The finite rope input produced from the fixed paired-return leaf. -/
noncomputable def rankThreeData (x : Input) : RankThreeInputData :=
  BenignMapEmbRopeInput.rankThreeData (mapEmbInput x)

/-- The resulting finite presentation code. -/
noncomputable def compile (x : Input) : PresentationCode :=
  MikhailovaRopeCode.compileRankThree (rankThreeData x)

@[simp] theorem rankThreeData_words (x : Input) :
    (rankThreeData x).2.2 =
      (DirectProductCode.rightWord ambientCode x.1 x.2.2.1,
        (DirectProductCode.rightWord ambientCode x.1 x.2.2.2.1,
          DirectProductCode.rightWord ambientCode x.1 x.2.2.2.2)) := by
  apply BenignMapEmbRopeInput.rankThreeData_words_of_exact
  rfl

@[simp] theorem rankThreeData_cutting (x : Input) :
    (rankThreeData x).2.1 =
      fiveWords.map (DirectProductCode.leftWord ambientCode) := rfl

theorem primrec_targetGeneratorWord (i : ℕ) :
    Primrec (fun x : Input => targetGeneratorWord x i) :=
  (Primrec.list_getD []).comp
    (Primrec.fst.comp Primrec.snd) (Primrec.const i)

theorem primrec_fixedAmbientGeneratorWord (i : ℕ) :
    Primrec (fun _ : PUnit => fixedAmbientGeneratorWord i) :=
  Primrec.const _

theorem primrec_edgePair (i : ℕ) :
    Primrec (fun x : Input =>
      (fixedAmbientGeneratorWord i, targetGeneratorWord x i)) :=
  Primrec.pair (Primrec.const _) (primrec_targetGeneratorWord i)

theorem primrec_edgePairs : Primrec edgePairs :=
  Primrec.list_cons.comp (primrec_edgePair 0)
    (Primrec.list_cons.comp (primrec_edgePair 1)
      (Primrec.list_cons.comp (primrec_edgePair 2)
        (Primrec.list_cons.comp (primrec_edgePair 3)
          (Primrec.list_cons.comp (primrec_edgePair 4)
            (Primrec.list_cons.comp (primrec_edgePair 5)
              (Primrec.const []))))))

theorem primrec_threeMarkedWords : Primrec threeMarkedWords := by
  have hzero : Primrec (fun x : Input => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hone : Primrec (fun x : Input => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htwo : Primrec (fun x : Input => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_cons.comp hzero
    (Primrec.list_cons.comp hone
      (Primrec.list_cons.comp htwo (Primrec.const [])))

theorem primrec_mapEmbInput : Primrec mapEmbInput := by
  have hdiagram : Primrec (fun x : Input =>
      ((ambientCode, x.1), edgePairs x)) :=
    Primrec.pair (Primrec.pair (Primrec.const _) Primrec.fst) primrec_edgePairs
  have hwords : Primrec (fun x : Input =>
      (fiveWords, threeMarkedWords x)) :=
    Primrec.pair (Primrec.const _) primrec_threeMarkedWords
  exact Primrec.pair hdiagram hwords

theorem primrec_rankThreeData : Primrec rankThreeData :=
  BenignMapEmbRopeInput.primrec_rankThreeData.comp primrec_mapEmbInput

theorem computable_rankThreeData : Computable rankThreeData :=
  primrec_rankThreeData.to_comp

theorem primrec_compile : Primrec compile :=
  MikhailovaRopeCode.primrec_compileRankThree.comp primrec_rankThreeData

theorem computable_compile : Computable compile :=
  primrec_compile.to_comp

end PairedReturnMapEmbCode
end Higman
end GroupApproximation
