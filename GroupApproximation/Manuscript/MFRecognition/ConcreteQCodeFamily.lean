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

/-- Reading the concrete bridge program through the manuscript's standard
relator decoder produces exactly the bridge-kernel relators, together with
the harmless identity contributed by bounded-evaluator failures. -/
theorem rank3Relators_qcode_eq (e : Nat.Partrec.Code) :
    rank3Relators (qcode e) =
      Higman.BridgeRelatorCode.rankThreeRelatorSet
          (RecursiveSwitchPresentation.switchEnumeratorCode e) ∪ {1} := by
  let c := RecursiveSwitchPresentation.switchEnumeratorCode e
  ext x
  constructor
  · rintro ⟨encodedAddress, rfl⟩
    let p := Nat.unpair encodedAddress
    cases heval : Nat.Partrec.Code.evaln p.2 (qcode e) p.1 with
    | none =>
        apply Or.inr
        simp [rank3Word,
          EnumeratedPresentationCodes.rawRelator, p, heval,
          Higman.Transport.rawToFree_nil]
    | some y =>
        have hsound : y ∈ Nat.Partrec.Code.eval (qcode e) p.1 :=
          Nat.Partrec.Code.evaln_sound heval
        rw [qcode, Higman.BridgeRelatorCode.eval_rankThreeCode] at hsound
        have hy : y = Encodable.encode
            (Higman.BridgeRelatorCode.rankThreeRawRelator c p.1) := by
          simpa [c] using hsound
        apply Or.inl
        refine ⟨p.1, ?_⟩
        simp [rank3Word,
          EnumeratedPresentationCodes.rawRelator,
          EnumeratedPresentationCodes.decodeRawWord, p, heval, hy, c]
  · rintro (hx | hx)
    · obtain ⟨address, rfl⟩ := hx
      have hmem : Encodable.encode
          (Higman.BridgeRelatorCode.rankThreeRawRelator c address) ∈
          Nat.Partrec.Code.eval (qcode e) address := by
        rw [qcode, Higman.BridgeRelatorCode.eval_rankThreeCode]
        exact Part.mem_some _
      obtain ⟨stage, hstage⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
      have hstage' : Nat.Partrec.Code.evaln stage (qcode e) address =
          some (Encodable.encode
            (Higman.BridgeRelatorCode.rankThreeRawRelator c address)) := hstage
      refine ⟨Nat.pair address stage, ?_⟩
      simp [rank3Word,
        EnumeratedPresentationCodes.rawRelator,
        EnumeratedPresentationCodes.decodeRawWord, hstage', c]
    · have hxone : x = 1 := by simpa using hx
      subst x
      refine ⟨Nat.pair 0 0, ?_⟩
      change Higman.rawToFree 2
        ((Nat.Partrec.Code.evaln 0 (qcode e) 0).map
          EnumeratedPresentationCodes.decodeRawWord |>.getD []) = 1
      rw [RecursiveSwitchPresentation.evaln_zero_eq_none]
      exact Higman.Transport.rawToFree_nil 2

private theorem normalClosure_insert_one
    (S : Set Source) :
    Subgroup.normalClosure (S ∪ {1}) = Subgroup.normalClosure S := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x (hx | hx)
    · exact Subgroup.subset_normalClosure hx
    · have : x = 1 := by simpa using hx
      subst x
      exact Subgroup.one_mem _
  · exact Subgroup.normalClosure_mono Set.subset_union_left

/-- The manuscript kernel for the actual qcode is the literal kernel of the
once-only three-generator bridge map. -/
theorem kernelN_qcode_eq_bridgeKer (e : Nat.Partrec.Code) :
    kernelN (qcode e) =
      MonoidHom.ker
        (Higman.BridgeEff.pi3
          (Higman.BridgeRelatorCode.sourceGen
            (RecursiveSwitchPresentation.switchEnumeratorCode e))) := by
  rw [kernelN, rank3Relators_qcode_eq, normalClosure_insert_one]
  exact Higman.BridgeRelatorCode.normalClosure_rankThreeRelatorSet _

/-- End-to-end semantics of the concrete switch/bridge family: its presented
group is exactly the effective three-generator HNN bridge of the semantic
switch group. -/
noncomputable def presentedQEquivBridge (e : Nat.Partrec.Code) :
    PresentedQ (qcode e) ≃*
      Higman.HNNEmb.Ext
        (Higman.BridgeRelatorCode.sourceGen
          (RecursiveSwitchPresentation.switchEnumeratorCode e)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (by
        rw [rank3Relators_qcode_eq, normalClosure_insert_one])).trans
    (Higman.BridgeRelatorCode.rankThreePresentedEquiv
      (RecursiveSwitchPresentation.switchEnumeratorCode e))

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
