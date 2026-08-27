import GroupApproximation.Higman.ReifiedPrimitiveRecursiveTowerBase
import GroupApproximation.Computability.BenignInfCode

/-!
# Concrete coded witnesses for Higman's two atoms

The compositional effective layer works with `BenignInfCode.WitnessSyntax`,
not by merging completed HNN towers.  This file converts the already explicit
`Z` and `S` base gadgets into that real compiler state: an ambient finite
presentation, finitely many cutter words, and six source marks.  The first
three marks are the literal `a,b,c`; the final three are identities, matching
the six-mark product interface used by `TransportStarCode`.
-/

namespace GroupApproximation
namespace Higman
namespace ReifiedHigmanWitnessBaseCode

open ReifiedPrimrecTower

abbrev Raw := BenignInfCode.Raw
abbrev WitnessSyntax := BenignInfCode.WitnessSyntax

/-- Literal one-letter spelling of source generator `i`. -/
def sourceWord (i : ℕ) : Raw := [((i : ℕ), true)]

/-- Six-mark source interface: `a,b,c`, followed by three identities. -/
def sourceSixMarks : List Raw :=
  [sourceWord 0, sourceWord 1, sourceWord 2, [], [], []]

/-- Coded benign-witness syntax for `A_Z = ⟨a⟩ ≤ F₃`. -/
def zeroWitnessSyntax : WitnessSyntax :=
  (rankThreeBaseCode, ([aWord], sourceSixMarks))

/-- Coded benign-witness syntax for Higman's successor family inside the
literal flip-group presentation. -/
def successorWitnessSyntax : WitnessSyntax :=
  (successorBaseCode,
    ([successorOrbitWord, successorShiftWord], sourceSixMarks))

@[simp] theorem zeroWitnessSyntax_code :
    zeroWitnessSyntax.1 = rankThreeBaseCode := rfl

@[simp] theorem zeroWitnessSyntax_cutting :
    zeroWitnessSyntax.2.1 = [aWord] := rfl

@[simp] theorem successorWitnessSyntax_code :
    successorWitnessSyntax.1 = successorBaseCode := rfl

@[simp] theorem successorWitnessSyntax_cutting :
    successorWitnessSyntax.2.1 = [successorOrbitWord, successorShiftWord] := rfl

@[simp] theorem sourceSixMarks_length : sourceSixMarks.length = 6 := rfl

/-- Reified dispatch for the two atomic Higman witness programs. -/
def baseWitnessSyntax : Bool → WitnessSyntax
  | false => zeroWitnessSyntax
  | true => successorWitnessSyntax

theorem primrec_sourceWord : Primrec sourceWord :=
  Primrec.list_cons.comp (Primrec.pair Primrec.id (Primrec.const true))
    (Primrec.const [])

theorem primrec_sourceSixMarks :
    Primrec (fun _ : Unit => sourceSixMarks) := Primrec.const _

theorem primrec_zeroWitnessSyntax :
    Primrec (fun _ : Unit => zeroWitnessSyntax) := Primrec.const _

theorem primrec_successorWitnessSyntax :
    Primrec (fun _ : Unit => successorWitnessSyntax) := Primrec.const _

theorem primrec_baseWitnessSyntax : Primrec baseWitnessSyntax :=
  (Primrec.cond Primrec.id (Primrec.const successorWitnessSyntax)
    (Primrec.const zeroWitnessSyntax)).of_eq fun b => by cases b <;> rfl

theorem computable_baseWitnessSyntax : Computable baseWitnessSyntax :=
  primrec_baseWitnessSyntax.to_comp

end ReifiedHigmanWitnessBaseCode
end Higman
end GroupApproximation
