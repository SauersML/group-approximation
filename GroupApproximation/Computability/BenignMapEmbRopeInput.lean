import GroupApproximation.Computability.BenignMapEmbCode
import GroupApproximation.Higman.MikhailovaRopeCode

/-!
# Feed an effective benign image witness to the rank-three rope compiler

The preceding transformation outputs an ambient presentation, cutting words,
and marked ambient words.  The Mikhailova rope compiler consumes exactly the
first three marks, corresponding to the fixed free rank-three source.  This
module performs that final total, primitive-recursive assembly and immediately
feeds it to `compileRankThree`.
-/

namespace GroupApproximation
namespace BenignMapEmbRopeInput

open BenignMapEmbCode
open Higman.MikhailovaRopeCode

abbrev Raw : Type := BenignMapEmbCode.Raw

/-- Total extraction of the three ambient representatives used by the fixed
rank-three source.  Malformed short lists receive the empty-word default. -/
def firstThree (l : List Raw) : RankThreeWords :=
  (l.getD 0 [], (l.getD 1 [], l.getD 2 []))

@[simp] theorem firstThree_exact (u v w : Raw) :
    firstThree [u, v, w] = (u, (v, w)) := rfl

/-- The actual finite syntax input emitted after one varying `mapEmb` step. -/
def rankThreeData (x : BenignMapEmbCode.Input) : RankThreeInputData :=
  let y := BenignMapEmbCode.transform x
  (y.1, (y.2.1, firstThree y.2.2))

@[simp] theorem rankThreeData_ambient (x : BenignMapEmbCode.Input) :
    (rankThreeData x).1 =
      AmalgamCode.amalgamCode x.1.1.1 x.1.1.2 x.1.2 := rfl

@[simp] theorem rankThreeData_cutting (x : BenignMapEmbCode.Input) :
    (rankThreeData x).2.1 = BenignMapEmbCode.cuttingWords x := rfl

theorem rankThreeData_words_of_exact (x : BenignMapEmbCode.Input)
    (u v w : Raw) (h : BenignMapEmbCode.markedWords x = [u, v, w]) :
    (rankThreeData x).2.2 = (u, (v, w)) := by
  simp only [rankThreeData, BenignMapEmbCode.transform, h, firstThree_exact]

/-- One varying benign-image step followed by the finite rope presentation
compiler. -/
def compile (x : BenignMapEmbCode.Input) : PresentationCodes.PresentationCode :=
  compileRankThree (rankThreeData x)

theorem primrec_firstThree : Primrec firstThree := by
  have hzero : Primrec (fun l : List Raw => l.getD 0 []) :=
    (Primrec.list_getD []).comp Primrec.id (Primrec.const 0)
  have hone : Primrec (fun l : List Raw => l.getD 1 []) :=
    (Primrec.list_getD []).comp Primrec.id (Primrec.const 1)
  have htwo : Primrec (fun l : List Raw => l.getD 2 []) :=
    (Primrec.list_getD []).comp Primrec.id (Primrec.const 2)
  exact Primrec.pair hzero (Primrec.pair hone htwo)

theorem primrec_rankThreeData : Primrec rankThreeData := by
  have hy : Primrec BenignMapEmbCode.transform :=
    BenignMapEmbCode.primrec_transform
  have hambient : Primrec (fun x : BenignMapEmbCode.Input =>
      (BenignMapEmbCode.transform x).1) := Primrec.fst.comp hy
  have hcutting : Primrec (fun x : BenignMapEmbCode.Input =>
      (BenignMapEmbCode.transform x).2.1) :=
    (Primrec.fst.comp Primrec.snd).comp hy
  have hmarked : Primrec (fun x : BenignMapEmbCode.Input =>
      (BenignMapEmbCode.transform x).2.2) :=
    (Primrec.snd.comp Primrec.snd).comp hy
  exact Primrec.pair hambient
    (Primrec.pair hcutting (primrec_firstThree.comp hmarked))

theorem computable_rankThreeData : Computable rankThreeData :=
  primrec_rankThreeData.to_comp

theorem primrec_compile : Primrec compile :=
  primrec_compileRankThree.comp primrec_rankThreeData

theorem computable_compile : Computable compile :=
  primrec_compile.to_comp

end BenignMapEmbRopeInput
end GroupApproximation
