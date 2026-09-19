import GroupApproximation.Computability.RecursiveSwitchPresentation
import GroupApproximation.Manuscript.MFRecognition.FixedUniversalFamily
import GroupApproximation.Manuscript.MFRecognition.TwoSidedBridgeRelatorCode

/-!
# The concrete printed two-sided bridge family

The switch compiler produces a countable presentation at a program index.
`TwoSidedBridgeRelatorCode.rankThreeCode` then presents the literal manuscript
group `B(C_e)` on `x,y,t`.  This module records the numerical family and its
exact semantic equivalence; unlike the older auxiliary family, its carrier is
not the one-sided group `HNNEmb.Ext`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace TwoSidedConcreteQCodeFamily

noncomputable section

namespace TS
export TwoSidedBridgeRelatorCode
  (rankThreeCode computable_rankThreeCode rankThreeRelatorSet
    eval_rankThreeCode rankThreeRawRelator bridgeMap sourceGen
    normalClosure_rankThreeRelatorSet rankThreePresentedEquiv)
end TS

/-- The literal rank-three input at machine index `e`. -/
def qcode (e : Nat.Partrec.Code) : RecPresCode :=
  TS.rankThreeCode
    (RecursiveSwitchPresentation.switchEnumeratorCode e)

theorem computable_qcode : Computable qcode :=
  TS.computable_rankThreeCode.comp
    RecursiveSwitchPresentation.computable_switchEnumeratorCode

/-- Decoding the numerical program gives precisely its direct kernel range,
together with the harmless identity emitted by bounded-evaluator failures. -/
theorem rank3Relators_qcode_eq (e : Nat.Partrec.Code) :
    rank3Relators (qcode e) =
      TS.rankThreeRelatorSet
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
        rw [qcode, TS.eval_rankThreeCode] at hsound
        have hy : y = Encodable.encode (TS.rankThreeRawRelator c p.1) := by
          simpa [c] using hsound
        apply Or.inl
        refine ⟨p.1, ?_⟩
        simp [rank3Word,
          EnumeratedPresentationCodes.rawRelator,
          EnumeratedPresentationCodes.decodeRawWord, p, heval, hy, c]
  · rintro (hx | hx)
    · obtain ⟨address, rfl⟩ := hx
      have hmem : Encodable.encode (TS.rankThreeRawRelator c address) ∈
          Nat.Partrec.Code.eval (qcode e) address := by
        rw [qcode, TS.eval_rankThreeCode]
        exact Part.mem_some _
      obtain ⟨stage, hstage⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
      have hstage' : Nat.Partrec.Code.evaln stage (qcode e) address =
          some (Encodable.encode (TS.rankThreeRawRelator c address)) := hstage
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
      have hnone : Nat.Partrec.Code.evaln 0 (qcode e) 0 = Option.none := by
        cases h : Nat.Partrec.Code.evaln 0 (qcode e) 0 with
        | none => rfl
        | some y =>
            have hlt : 0 < 0 := Nat.Partrec.Code.evaln_bound h
            omega
      rw [hnone]
      exact Higman.Transport.rawToFree_nil 2

private theorem normalClosure_insert_one (S : Set Source) :
    Subgroup.normalClosure (S ∪ {1}) = Subgroup.normalClosure S := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x (hx | hx)
    · exact Subgroup.subset_normalClosure hx
    · have : x = 1 := by simpa using hx
      subst x
      exact Subgroup.one_mem _
  · exact Subgroup.normalClosure_mono Set.subset_union_left

/-- The manuscript kernel is the kernel of the literal `qC` bridge map. -/
theorem kernelN_qcode_eq_bridgeKer (e : Nat.Partrec.Code) :
    kernelN (qcode e) =
      MonoidHom.ker
        (TS.bridgeMap
          (RecursiveSwitchPresentation.switchEnumeratorCode e)) := by
  rw [kernelN, rank3Relators_qcode_eq, normalClosure_insert_one]
  exact TS.normalClosure_rankThreeRelatorSet _

/-- End-to-end semantics: the presented input is exactly the printed
two-sided bridge over the semantic switch carrier's canonical generators. -/
noncomputable def presentedQEquivBridge (e : Nat.Partrec.Code) :
    PresentedQ (qcode e) ≃*
      Bridge.BGroup
        (Bridge.seq
          (TS.sourceGen
            (RecursiveSwitchPresentation.switchEnumeratorCode e))) :=
  (QuotientGroup.quotientMulEquivOfEq
      (by rw [rank3Relators_qcode_eq, normalClosure_insert_one])).trans
    (TS.rankThreePresentedEquiv
      (RecursiveSwitchPresentation.switchEnumeratorCode e))

/-- Enumerate the code-indexed family by naturals for the once-only fixed
universal host. -/
def indexedQcode (n : ℕ) : RecPresCode :=
  qcode (Denumerable.ofNat Nat.Partrec.Code n)

theorem computable_indexedQcode : Computable indexedQcode :=
  computable_qcode.comp (Computable.ofNat Nat.Partrec.Code)

abbrev U : Type := FixedUniversalFamily.U indexedQcode

def sourceEmb (n : ℕ) : PresentedQ (indexedQcode n) →* U :=
  FixedUniversalFamily.sourceEmb indexedQcode n

theorem sourceEmb_injective (n : ℕ) : Function.Injective (sourceEmb n) :=
  FixedUniversalFamily.sourceEmb_injective indexedQcode n

end

end TwoSidedConcreteQCodeFamily
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
