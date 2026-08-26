import GroupApproximation.Computability.AmalgamCode

/-!
# Effective syntax for the benign image construction

`BenignWitness.mapEmb` replaces an old witness ambient `K` and a new ambient
`N` by their amalgam over the source group.  At presentation level the finite
data are: the two codes, displayed word pairs for generators of the glued
source, old cutting words in `K`, and marked words in `N`.  This module performs
that entire varying list transformation.  Its semantic identification is
provided separately by `AmalgamCodeSemantics` and the pushout bridge.
-/

namespace GroupApproximation
namespace BenignMapEmbCode

open PresentationCodes AmalgamCode RawTransformPrimrec

abbrev Raw : Type := AmalgamCode.Raw

/-- Two factor codes and the displayed gluing pairs. -/
abbrev Diagram : Type :=
  (PresentationCode × PresentationCode) × List (Raw × Raw)

/-- A mapEmb diagram, old cutting words, and marked words in the new factor. -/
abbrev Input : Type := Diagram × (List Raw × List Raw)

/-- Output ambient code, transported cutting words, and transported marks. -/
abbrev Output : Type := PresentationCode × (List Raw × List Raw)

def leftCode (x : Input) : PresentationCode := x.1.1.1

def rightCode (x : Input) : PresentationCode := x.1.1.2

theorem primrec_leftCode : Primrec leftCode :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.fst)

theorem primrec_rightCode : Primrec rightCode :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.fst)

/-- Put every old cutting word into the left factor alphabet. -/
def cuttingWords (x : Input) : List Raw :=
  x.2.1.map (DirectProductCode.leftWord (leftCode x))

theorem primrec_cuttingWord : Primrec
    (fun a : Input × Raw =>
      DirectProductCode.leftWord (leftCode a.1) a.2) :=
  Primrec₂.comp DirectProductCode.primrec_leftWord
    (primrec_leftCode.comp Primrec.fst)
    Primrec.snd

theorem primrec_cuttingWords : Primrec cuttingWords :=
  Primrec.list_map (Primrec.fst.comp Primrec.snd) primrec_cuttingWord

def markedWordInput (a : Input × Raw) :
    (PresentationCode × PresentationCode) × Raw :=
  ((leftCode a.1, rightCode a.1), a.2)

theorem primrec_markedWordInput : Primrec markedWordInput :=
  Primrec.pair
    (Primrec.pair
      (primrec_leftCode.comp Primrec.fst)
      (primrec_rightCode.comp Primrec.fst))
    Primrec.snd

def markedWord (a : Input × Raw) : Raw :=
  DirectProductCode.rightWord (markedWordInput a).1.1
    (markedWordInput a).1.2 (markedWordInput a).2

theorem primrec_markedWord : Primrec markedWord :=
  DirectProductCode.primrec_rightWord.comp primrec_markedWordInput

/-- Put every marked word into the right factor alphabet. -/
def markedWords (x : Input) : List Raw :=
  x.2.2.map fun w => markedWord (x, w)

theorem primrec_markedWords : Primrec markedWords :=
  Primrec.list_map (Primrec.snd.comp Primrec.snd) primrec_markedWord

/-- The complete code-level image-witness transformation. -/
def transform (x : Input) : Output :=
  (amalgamCode x.1.1.1 x.1.1.2 x.1.2,
    (cuttingWords x, markedWords x))

@[simp] theorem transform_code (x : Input) :
    (transform x).1 = amalgamCode x.1.1.1 x.1.1.2 x.1.2 := rfl

@[simp] theorem transform_cuttingWords (x : Input) :
    (transform x).2.1 =
      x.2.1.map (DirectProductCode.leftWord x.1.1.1) := rfl

@[simp] theorem transform_markedWords (x : Input) :
    (transform x).2.2 =
      x.2.2.map (DirectProductCode.rightWord x.1.1.1 x.1.1.2) := rfl

/-- The varying benign image transformation is primitive recursive. -/
theorem primrec_transform : Primrec transform := by
  have hcode : Primrec (fun x : Input =>
      amalgamCode x.1.1.1 x.1.1.2 x.1.2) :=
    primrec_amalgamCode.comp Primrec.fst
  exact Primrec.pair hcode
    (Primrec.pair primrec_cuttingWords primrec_markedWords)

theorem computable_transform : Computable transform :=
  primrec_transform.to_comp

end BenignMapEmbCode
end GroupApproximation
