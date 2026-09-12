import GroupApproximation.Higman.ReifiedHigmanWitnessBaseCode
import GroupApproximation.Computability.RawTransformPrimrec

/-!
# Effective witness syntax for Higman's shift

Transporting the witness uses the inverse of the automorphism realizing `σ`;
it fixes `a,c` and sends `b` to `cbc⁻¹`.
For a coded witness, the ambient presentation and cutter therefore stay
unchanged; only each marked rank-three source triple is rewritten.  The
six-mark interface contains two triples, so this transform applies the same
literal substitution to positions `0,1,2` and `3,4,5`.
-/

namespace GroupApproximation
namespace Higman
namespace ReifiedHigmanWitnessSigmaCode

open ReifiedHigmanWitnessBaseCode
open GroupApproximation.RawWord

abbrev Raw := BenignInfCode.Raw
abbrev WitnessSyntax := BenignInfCode.WitnessSyntax

/-- One marked word, with a harmless identity default for malformed lists. -/
def markAt (x : WitnessSyntax) (i : ℕ) : Raw := x.2.2.getD i []

/-- The word-level substitution `b ↦ cbc⁻¹`. -/
def shiftedMiddle (x : WitnessSyntax) (b c : ℕ) : Raw :=
  markAt x c ++ markAt x b ++ invWord (markAt x c)

/-- Rewritten six-mark interface for `σ`. -/
def sigmaMarks (x : WitnessSyntax) : List Raw :=
  [markAt x 0, shiftedMiddle x 1 2, markAt x 2,
    markAt x 3, shiftedMiddle x 4 5, markAt x 5]

/-- **Concrete code transform for `σ`.** -/
def transform (x : WitnessSyntax) : WitnessSyntax :=
  (x.1, (x.2.1, sigmaMarks x))

@[simp] theorem transform_code (x : WitnessSyntax) : (transform x).1 = x.1 := rfl

@[simp] theorem transform_cutting (x : WitnessSyntax) :
    (transform x).2.1 = x.2.1 := rfl

@[simp] theorem transform_marks (x : WitnessSyntax) :
    (transform x).2.2 = sigmaMarks x := rfl

theorem primrec_markAt (i : ℕ) :
    Primrec (fun x : WitnessSyntax => markAt x i) :=
  (Primrec.list_getD []).comp (Primrec.snd.comp Primrec.snd)
    (Primrec.const i)

theorem primrec_shiftedMiddle (b c : ℕ) :
    Primrec (fun x : WitnessSyntax => shiftedMiddle x b c) := by
  have hc : Primrec (fun x : WitnessSyntax => markAt x c) := primrec_markAt c
  have hinv : Primrec (fun x : WitnessSyntax => invWord (markAt x c)) :=
    RawTransformPrimrec.primrec_invWord.comp hc
  have hleft : Primrec (fun x : WitnessSyntax =>
      markAt x c ++ markAt x b) :=
    Primrec.list_append.comp hc (primrec_markAt b)
  exact Primrec.list_append.comp hleft hinv

theorem primrec_sigmaMarks : Primrec sigmaMarks :=
  Primrec.list_cons.comp (primrec_markAt 0)
    (Primrec.list_cons.comp (primrec_shiftedMiddle 1 2)
      (Primrec.list_cons.comp (primrec_markAt 2)
        (Primrec.list_cons.comp (primrec_markAt 3)
          (Primrec.list_cons.comp (primrec_shiftedMiddle 4 5)
            (Primrec.list_cons.comp (primrec_markAt 5)
              (Primrec.const []))))))

theorem primrec_transform : Primrec transform :=
  Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd) primrec_sigmaMarks)

theorem computable_transform : Computable transform :=
  primrec_transform.to_comp

end ReifiedHigmanWitnessSigmaCode
end Higman
end GroupApproximation
