import GroupApproximation.Higman.ReifiedHigmanWitnessBaseCode
import GroupApproximation.Computability.BenignMapEmbCode

/-!
# Effective witness syntax for Higman's reflection

The group-level `ρ` construction embeds the old witness and the displayed
flip group into their amalgam over `F₃`.  The gluing pairs identify the first
three old marks with `a,b,c` in the flip presentation.  The new source copy is
spelled by `a,β⁻¹,γ⁻¹`: `rhoAut` inverts `b,c`, and the flip exchanges
them with `β,γ`.  This file performs that exact finite word transformation.
-/

namespace GroupApproximation
namespace Higman
namespace ReifiedHigmanWitnessRhoCode

open ReifiedPrimrecTower ReifiedHigmanWitnessBaseCode

abbrev Raw := BenignInfCode.Raw
abbrev WitnessSyntax := BenignInfCode.WitnessSyntax

def oldMark (x : WitnessSyntax) (i : ℕ) : Raw := x.2.2.getD i []

def flipGeneratorWord (i : ℕ) : Raw := [((i : ℕ), true)]

/-- Identify the old marked `a,b,c` with the first three flip-group
generators. -/
def gluingPairs (x : WitnessSyntax) : List (Raw × Raw) :=
  [(oldMark x 0, flipGeneratorWord 0),
    (oldMark x 1, flipGeneratorWord 1),
    (oldMark x 2, flipGeneratorWord 2)]

/-- The reflected source marks `a,β⁻¹,γ⁻¹`, followed by the three
identity padding marks of the rank-three witness interface. -/
def rhoMarks : List Raw :=
  [[((0 : ℕ), true)], [((3 : ℕ), false)], [((4 : ℕ), false)], [], [], []]

def mapEmbInput (x : WitnessSyntax) : BenignMapEmbCode.Input :=
  (((x.1, successorBaseCode), gluingPairs x), (x.2.1, rhoMarks))

/-- **Concrete code transform for `ρ`.** -/
def transform (x : WitnessSyntax) : WitnessSyntax :=
  BenignMapEmbCode.transform (mapEmbInput x)

@[simp] theorem transform_cutting (x : WitnessSyntax) :
    (transform x).2.1 = BenignMapEmbCode.cuttingWords (mapEmbInput x) := rfl

@[simp] theorem transform_marks (x : WitnessSyntax) :
    (transform x).2.2 = BenignMapEmbCode.markedWords (mapEmbInput x) := rfl

theorem primrec_oldMark (i : ℕ) :
    Primrec (fun x : WitnessSyntax => oldMark x i) :=
  (Primrec.list_getD []).comp (Primrec.snd.comp Primrec.snd)
    (Primrec.const i)

theorem primrec_flipGeneratorWord : Primrec flipGeneratorWord :=
  Primrec.list_cons.comp (Primrec.pair Primrec.id (Primrec.const true))
    (Primrec.const [])

theorem primrec_gluingPair (i : ℕ) :
    Primrec (fun x : WitnessSyntax =>
      (oldMark x i, flipGeneratorWord i)) :=
  Primrec.pair (primrec_oldMark i)
    (primrec_flipGeneratorWord.comp (Primrec.const i))

theorem primrec_gluingPairs : Primrec gluingPairs :=
  Primrec.list_cons.comp (primrec_gluingPair 0)
    (Primrec.list_cons.comp (primrec_gluingPair 1)
      (Primrec.list_cons.comp (primrec_gluingPair 2) (Primrec.const [])))

theorem primrec_mapEmbInput : Primrec mapEmbInput := by
  have hdiagram : Primrec (fun x : WitnessSyntax =>
      ((x.1, successorBaseCode), gluingPairs x)) :=
    Primrec.pair (Primrec.pair Primrec.fst (Primrec.const successorBaseCode))
      primrec_gluingPairs
  have hpayload : Primrec (fun x : WitnessSyntax => (x.2.1, rhoMarks)) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.const rhoMarks)
  exact Primrec.pair hdiagram hpayload

theorem primrec_transform : Primrec transform :=
  BenignMapEmbCode.primrec_transform.comp primrec_mapEmbInput

theorem computable_transform : Computable transform :=
  primrec_transform.to_comp

end ReifiedHigmanWitnessRhoCode
end Higman
end GroupApproximation
