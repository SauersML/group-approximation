import GroupApproximation.Computability.RecursiveSwitchPresentation
import GroupApproximation.Higman.BridgeRelatorCode
import GroupApproximation.Manuscript.MFRecognition.FixedUniversalFamily

/-!
# The concrete rank-three input family

This is the single numerical family used by the recognition reduction.  The
switch program first produces the countable recursive presentation attached
to the machine index, and the effective HNN bridge then compiles its exact
three-generator kernel.  Keeping the composite under one name prevents the
fixed-host construction from being parameterized by an unspecified family.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace ConcreteQCodeFamily

noncomputable section

/-- The actual rank-three recursively presented group code at machine index
`e`. -/
def qcode (e : Nat.Partrec.Code) : RecPresCode :=
  Higman.BridgeRelatorCode.rankThreeCode
    (RecursiveSwitchPresentation.switchEnumeratorCode e)

theorem computable_qcode : Computable qcode :=
  Higman.BridgeRelatorCode.computable_rankThreeCode.comp
    RecursiveSwitchPresentation.computable_switchEnumeratorCode

/-- A natural-number enumeration of the actual code-indexed family.  This is
used only by the fixed universal host that witnesses computability; the
positive profinite path remains indexed by `Nat.Partrec.Code` itself. -/
def indexedQcode (n : ℕ) : RecPresCode :=
  qcode (Denumerable.ofNat Nat.Partrec.Code n)

theorem computable_indexedQcode : Computable indexedQcode :=
  computable_qcode.comp (Computable.ofNat Nat.Partrec.Code)

/-- The fixed universal group used by the computability-only compiler. -/
abbrev U : Type := FixedUniversalFamily.U indexedQcode

/-- Every concrete input group embeds canonically in that one group. -/
def sourceEmb (n : ℕ) : PresentedQ (indexedQcode n) →* U :=
  FixedUniversalFamily.sourceEmb indexedQcode n

theorem sourceEmb_injective (n : ℕ) : Function.Injective (sourceEmb n) :=
  FixedUniversalFamily.sourceEmb_injective indexedQcode n

end

end ConcreteQCodeFamily
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
