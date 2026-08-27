import GroupApproximation.Higman.MikhailovaRopeCode
import GroupApproximation.Computability.DirectProductCode

/-!
# Effective rank-three Mikhailova witness syntax

An effective Higman embedding supplies a finite presentation and three raw
words representing the images of the rank-three source generators.  The
Mikhailova fibre-product construction then has no further infinitary input.
This file performs that finite transformation explicitly.

For a host presentation `H = <X | R>`, the output ambient presents

`F₃ × (F(X) × F(X))`.

Its cutting list consists of the three generators of the first factor, the
diagonal pairs `(x,x)`, and the relator pairs `(r,1)`.  The three marked words
are `(a_i,w_i,1)`.  These are exactly the finite data consumed by
`MikhailovaRopeCode.RankThreeInputData`.
-/

namespace GroupApproximation
namespace Higman
namespace MikhailovaRankThreeCode

open PresentationCodes DirectProductCode RawTransformPrimrec
open MikhailovaRopeCode

abbrev Raw : Type := List (ℕ × Bool)

/-- A finite host presentation and the three words spelling the marked
rank-three embedding in that host. -/
abbrev Input : Type := PresentationCode × RankThreeWords

/-- The relator-free presentation on the host alphabet. -/
def hostFreeCode (x : Input) : PresentationCode :=
  presentationSkeleton x.1.1

/-- The two free host-alphabet factors used by Mikhailova's fibre product. -/
def hostPairCode (x : Input) : PresentationCode :=
  productCode (hostFreeCode x) (hostFreeCode x)

/-- The full Mikhailova ambient `F₃ × (F(X) × F(X))`. -/
def ambientCode (x : Input) : PresentationCode :=
  productCode (presentationSkeleton 2) (hostPairCode x)

/-- Put a host-alphabet word in the first free host factor. -/
def pairLeftWord (x : Input) (w : Raw) : Raw :=
  leftWord (hostFreeCode x) w

/-- Put a host-alphabet word in the second free host factor. -/
def pairRightWord (x : Input) (w : Raw) : Raw :=
  rightWord (hostFreeCode x) (hostFreeCode x) w

/-- Put a word of the free host pair in the right factor of the full ambient. -/
def ambientPairWord (x : Input) (w : Raw) : Raw :=
  rightWord (presentationSkeleton 2) (hostPairCode x) w

/-- Put a rank-three source word in the left factor of the full ambient. -/
def ambientSourceWord (w : Raw) : Raw :=
  leftWord (presentationSkeleton 2) w

/-- The word representing `(x_i,x_i)` in the free host pair. -/
def diagonalWord (x : Input) (i : ℕ) : Raw :=
  pairLeftWord x (rankThreeGeneratorWord i) ++
    pairRightWord x (rankThreeGeneratorWord i)

/-- The three generators of the whole rank-three first factor. -/
def sourceCuttingWords : List Raw :=
  (List.range 3).map fun i => ambientSourceWord (rankThreeGeneratorWord i)

/-- The diagonal generators `(x_i,x_i)` of the Mikhailova subgroup. -/
def diagonalCuttingWords (x : Input) : List Raw :=
  (List.range (genCount x.1)).map fun i => ambientPairWord x (diagonalWord x i)

/-- The generators `(r,1)` contributed by the finite host relators. -/
def relatorCuttingWords (x : Input) : List Raw :=
  x.1.2.map fun r => ambientPairWord x (pairLeftWord x r)

/-- A finite generating list for `F₃ × M_H`. -/
def cuttingWords (x : Input) : List Raw :=
  sourceCuttingWords ++ diagonalCuttingWords x ++ relatorCuttingWords x

/-- The ambient spelling of `(a_i,w,1)`. -/
def markedAmbientWord (x : Input) (i : ℕ) (w : Raw) : Raw :=
  ambientSourceWord (rankThreeGeneratorWord i) ++
    ambientPairWord x (pairLeftWord x w)

/-- The first marked ambient word. -/
def markedZero (x : Input) : Raw := markedAmbientWord x 0 x.2.1

/-- The second marked ambient word. -/
def markedOne (x : Input) : Raw := markedAmbientWord x 1 x.2.2.1

/-- The third marked ambient word. -/
def markedTwo (x : Input) : Raw := markedAmbientWord x 2 x.2.2.2

/-- The three marked ambient words. -/
def markedWords (x : Input) : RankThreeWords :=
  (markedZero x, (markedOne x, markedTwo x))

/-- **The exact finite syntax emitted after a marked effective Higman
embedding.** -/
def rankThreeData (x : Input) : RankThreeInputData :=
  (ambientCode x, (cuttingWords x, markedWords x))

@[simp] theorem rankThreeData_ambient (x : Input) :
    (rankThreeData x).1 = ambientCode x := rfl

@[simp] theorem rankThreeData_cutting (x : Input) :
    (rankThreeData x).2.1 = cuttingWords x := rfl

@[simp] theorem rankThreeData_words (x : Input) :
    (rankThreeData x).2.2 = markedWords x := rfl

/-! ## Primitive recursiveness -/

theorem primrec_hostFreeCode : Primrec hostFreeCode :=
  primrec_presentationSkeleton.comp (Primrec.fst.comp Primrec.fst)

theorem primrec_hostPairCode : Primrec hostPairCode :=
  primrec_productCode.comp
    (Primrec.pair primrec_hostFreeCode primrec_hostFreeCode)

theorem primrec_ambientCode : Primrec ambientCode :=
  primrec_productCode.comp
    (Primrec.pair (Primrec.const (presentationSkeleton 2))
      primrec_hostPairCode)

theorem primrec_pairLeftWord :
    Primrec (fun z : Input × Raw => pairLeftWord z.1 z.2) :=
  (Primrec₂.comp DirectProductCode.primrec_leftWord
    (primrec_hostFreeCode.comp Primrec.fst) Primrec.snd).of_eq fun _ => rfl

theorem primrec_pairRightWord :
    Primrec (fun z : Input × Raw => pairRightWord z.1 z.2) := by
  exact primrec_rightWord.comp
    (Primrec.pair
      (Primrec.pair (primrec_hostFreeCode.comp Primrec.fst)
        (primrec_hostFreeCode.comp Primrec.fst))
      Primrec.snd)

theorem primrec_ambientPairWord :
    Primrec (fun z : Input × Raw => ambientPairWord z.1 z.2) := by
  exact primrec_rightWord.comp
    (Primrec.pair
      (Primrec.pair (Primrec.const (presentationSkeleton 2))
        (primrec_hostPairCode.comp Primrec.fst))
      Primrec.snd)

theorem primrec_ambientSourceWord : Primrec ambientSourceWord :=
  (Primrec₂.comp DirectProductCode.primrec_leftWord
    (Primrec.const (presentationSkeleton 2)) Primrec.id).of_eq fun _ => rfl

theorem primrec_diagonalWord :
    Primrec (fun z : Input × ℕ => diagonalWord z.1 z.2) := by
  have hletter : Primrec (fun z : Input × ℕ => rankThreeGeneratorWord z.2) :=
    primrec_rankThreeGeneratorWord.comp Primrec.snd
  have hleft : Primrec (fun z : Input × ℕ =>
      pairLeftWord z.1 (rankThreeGeneratorWord z.2)) :=
    primrec_pairLeftWord.comp (Primrec.pair Primrec.fst hletter)
  have hright : Primrec (fun z : Input × ℕ =>
      pairRightWord z.1 (rankThreeGeneratorWord z.2)) :=
    primrec_pairRightWord.comp (Primrec.pair Primrec.fst hletter)
  exact Primrec.list_append.comp hleft hright

theorem primrec_sourceCuttingWords :
    Primrec (fun _ : PUnit => sourceCuttingWords) := Primrec.const _

theorem primrec_diagonalCuttingWords : Primrec diagonalCuttingWords := by
  have hrange : Primrec (fun x : Input => List.range (genCount x.1)) :=
    Primrec.list_range.comp
      (RawTransformPrimrec.primrec_genCount.comp Primrec.fst)
  have hword : Primrec (fun z : Input × ℕ =>
      ambientPairWord z.1 (diagonalWord z.1 z.2)) :=
    primrec_ambientPairWord.comp
      (Primrec.pair Primrec.fst (primrec_diagonalWord.comp Primrec.id))
  exact Primrec.list_map hrange hword

theorem primrec_relatorCuttingWords : Primrec relatorCuttingWords := by
  have hrels : Primrec (fun x : Input => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hword : Primrec (fun z : Input × Raw =>
      ambientPairWord z.1 (pairLeftWord z.1 z.2)) :=
    primrec_ambientPairWord.comp
      (Primrec.pair Primrec.fst (primrec_pairLeftWord.comp Primrec.id))
  exact Primrec.list_map hrels hword

theorem primrec_cuttingWords : Primrec cuttingWords := by
  have hhead : Primrec (fun x : Input =>
      sourceCuttingWords ++ diagonalCuttingWords x) :=
    Primrec₂.comp Primrec.list_append (Primrec.const sourceCuttingWords)
      primrec_diagonalCuttingWords
  exact Primrec₂.comp Primrec.list_append hhead primrec_relatorCuttingWords

theorem primrec_markedAmbientWord (i : ℕ) :
    Primrec (fun z : Input × Raw => markedAmbientWord z.1 i z.2) := by
  have hsource : Primrec (fun _ : Input × Raw =>
      ambientSourceWord (rankThreeGeneratorWord i)) := Primrec.const _
  have hright : Primrec (fun z : Input × Raw =>
      ambientPairWord z.1 (pairLeftWord z.1 z.2)) :=
    primrec_ambientPairWord.comp
      (Primrec.pair Primrec.fst (primrec_pairLeftWord.comp Primrec.id))
  exact Primrec.list_append.comp hsource hright

theorem primrec_markedWords : Primrec markedWords := by
  have hzero : Primrec markedZero :=
    ((primrec_markedAmbientWord 0).comp
      (Primrec.pair Primrec.id (Primrec.fst.comp Primrec.snd))).of_eq
        fun _ => rfl
  have hone : Primrec markedOne :=
    ((primrec_markedAmbientWord 1).comp
      (Primrec.pair Primrec.id
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).of_eq
          fun _ => rfl
  have htwo : Primrec markedTwo :=
    ((primrec_markedAmbientWord 2).comp
      (Primrec.pair Primrec.id
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).of_eq
          fun _ => rfl
  exact Primrec.pair hzero (Primrec.pair hone htwo)

theorem primrec_rankThreeData : Primrec rankThreeData :=
  Primrec.pair primrec_ambientCode
    (Primrec.pair primrec_cuttingWords primrec_markedWords)

theorem computable_rankThreeData : Computable rankThreeData :=
  primrec_rankThreeData.to_comp

/-- The full rope presentation after the closed Mikhailova syntax stage. -/
def compile (x : Input) : PresentationCode :=
  MikhailovaRopeCode.compileRankThree (rankThreeData x)

theorem primrec_compile : Primrec compile :=
  MikhailovaRopeCode.primrec_compileRankThree.comp primrec_rankThreeData

theorem computable_compile : Computable compile :=
  primrec_compile.to_comp

end MikhailovaRankThreeCode
end Higman
end GroupApproximation
