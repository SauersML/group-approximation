import GroupApproximation.Higman.PairedReturnCutterCode
import GroupApproximation.Computability.BenignInfCode
import GroupApproximation.Computability.BenignSupCode
import GroupApproximation.Computability.BenignComapCode
import GroupApproximation.Computability.BenignComapThreeCode
import GroupApproximation.Computability.BenignMapEmbRopeInput

/-!
# Effective syntax for the proved TransportStar witness calculus

Starting from a coded rank-three benign witness, this module follows the
literal construction in `TransportStar.benignTF_map_evalHom`: comap to
`F₃ × F₃`, intersect with the fixed paired-return graph witness, join the
fixed `F₃ × 1` subgroup, and comap along the right inclusion.  The result is
immediately packaged as `RankThreeInputData` and compiled.
-/

namespace GroupApproximation
namespace Higman
namespace TransportStarCode

open PresentationCodes
open MikhailovaRopeCode
open PairedReturnCutterCode

abbrev Raw : Type := List (ℕ × Bool)
abbrev Input : Type := RankThreeInputData
abbrev WitnessSyntax : Type := BenignInfCode.WitnessSyntax

def inputMarks (x : Input) : List Raw :=
  [x.2.2.1, x.2.2.2.1, x.2.2.2.2]

def productInputMarks (x : Input) : List Raw :=
  [x.2.2.1, x.2.2.2.1, x.2.2.2.2, [], [], []]

noncomputable def productOvergroupSyntax : WitnessSyntax :=
  (pCode, ([], pGeneratorWords))

def varyingProductSyntax (x : Input) : WitnessSyntax :=
  (x.1, (x.2.1, productInputMarks x))

noncomputable def graphSyntax : WitnessSyntax :=
  (ambientCode, (fiveWords, ambientPGeneratorWords))

noncomputable def botSyntax : WitnessSyntax :=
  (pCode, (pGeneratorWords.take 3, pGeneratorWords))

noncomputable def hprod (x : Input) : WitnessSyntax :=
  BenignComapCode.transform (productOvergroupSyntax, varyingProductSyntax x)

noncomputable def hgamma (x : Input) : WitnessSyntax :=
  BenignInfCode.transform (graphSyntax, hprod x)

noncomputable def hjoin (x : Input) : WitnessSyntax :=
  BenignSupCode.transform (hgamma x, botSyntax)

def lastThreeMarks (w : WitnessSyntax) : List Raw :=
  [w.2.2.getD 3 [], w.2.2.getD 4 [], w.2.2.getD 5 []]

def freeRankThreeSyntax : WitnessSyntax :=
  (presentationSkeleton 2,
    ([], [rankThreeGeneratorWord 0, rankThreeGeneratorWord 1,
      rankThreeGeneratorWord 2]))

noncomputable def finalRightSyntax (x : Input) : WitnessSyntax :=
  ((hjoin x).1, ((hjoin x).2.1, lastThreeMarks (hjoin x)))

noncomputable def transportedSyntax (x : Input) : WitnessSyntax :=
  BenignComapThreeCode.transform (freeRankThreeSyntax, finalRightSyntax x)

/-- The concrete finite rope input emitted by the TransportStar code path. -/
noncomputable def rankThreeData (x : Input) : RankThreeInputData :=
  let y := transportedSyntax x
  (y.1, (y.2.1, BenignMapEmbRopeInput.firstThree y.2.2))

noncomputable def compile (x : Input) : PresentationCode :=
  compileRankThree (rankThreeData x)

theorem primrec_inputMarks : Primrec inputMarks := by
  have h0 : Primrec (fun x : Input => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h1 : Primrec (fun x : Input => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h2 : Primrec (fun x : Input => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_cons.comp h0
    (Primrec.list_cons.comp h1
      (Primrec.list_cons.comp h2 (Primrec.const [])))

theorem primrec_productInputMarks : Primrec productInputMarks := by
  have h := primrec_inputMarks
  exact (Primrec.list_append.comp h (Primrec.const [[], [], []])).of_eq
    fun _ => rfl

theorem primrec_varyingProductSyntax : Primrec varyingProductSyntax :=
  Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd) primrec_productInputMarks)

theorem primrec_productOvergroupSyntax :
    Primrec (fun _ : PUnit => productOvergroupSyntax) := Primrec.const _

theorem primrec_graphSyntax :
    Primrec (fun _ : PUnit => graphSyntax) := Primrec.const _

theorem primrec_botSyntax :
    Primrec (fun _ : PUnit => botSyntax) := Primrec.const _

theorem primrec_hprod : Primrec hprod :=
  BenignComapCode.primrec_transform.comp
    (Primrec.pair (Primrec.const _) primrec_varyingProductSyntax)

theorem primrec_hgamma : Primrec hgamma :=
  BenignInfCode.primrec_transform.comp
    (Primrec.pair (Primrec.const _) primrec_hprod)

theorem primrec_hjoin : Primrec hjoin :=
  BenignSupCode.primrec_transform.comp
    (Primrec.pair primrec_hgamma (Primrec.const _))

theorem primrec_lastThreeMarks : Primrec lastThreeMarks := by
  have h3 : Primrec (fun w : WitnessSyntax => w.2.2.getD 3 []) :=
    (Primrec.list_getD []).comp (Primrec.snd.comp Primrec.snd)
      (Primrec.const 3)
  have h4 : Primrec (fun w : WitnessSyntax => w.2.2.getD 4 []) :=
    (Primrec.list_getD []).comp (Primrec.snd.comp Primrec.snd)
      (Primrec.const 4)
  have h5 : Primrec (fun w : WitnessSyntax => w.2.2.getD 5 []) :=
    (Primrec.list_getD []).comp (Primrec.snd.comp Primrec.snd)
      (Primrec.const 5)
  exact Primrec.list_cons.comp h3
    (Primrec.list_cons.comp h4
      (Primrec.list_cons.comp h5 (Primrec.const [])))

theorem primrec_freeRankThreeSyntax :
    Primrec (fun _ : PUnit => freeRankThreeSyntax) := Primrec.const _

theorem primrec_finalRightSyntax : Primrec finalRightSyntax :=
  Primrec.pair (Primrec.fst.comp primrec_hjoin)
    (Primrec.pair ((Primrec.fst.comp Primrec.snd).comp primrec_hjoin)
      (primrec_lastThreeMarks.comp primrec_hjoin))

theorem primrec_transportedSyntax : Primrec transportedSyntax :=
  BenignComapThreeCode.primrec_transform.comp
    (Primrec.pair (Primrec.const _) primrec_finalRightSyntax)

theorem primrec_rankThreeData : Primrec rankThreeData := by
  have ha : Primrec (fun x : Input => (transportedSyntax x).1) :=
    Primrec.fst.comp primrec_transportedSyntax
  have hc : Primrec (fun x : Input => (transportedSyntax x).2.1) :=
    (Primrec.fst.comp Primrec.snd).comp primrec_transportedSyntax
  have hm : Primrec (fun x : Input => (transportedSyntax x).2.2) :=
    (Primrec.snd.comp Primrec.snd).comp primrec_transportedSyntax
  exact Primrec.pair ha
    (Primrec.pair hc (BenignMapEmbRopeInput.primrec_firstThree.comp hm))

theorem computable_rankThreeData : Computable rankThreeData :=
  primrec_rankThreeData.to_comp

theorem primrec_compile : Primrec compile :=
  primrec_compileRankThree.comp primrec_rankThreeData

theorem computable_compile : Computable compile :=
  primrec_compile.to_comp

end TransportStarCode
end Higman
end GroupApproximation
