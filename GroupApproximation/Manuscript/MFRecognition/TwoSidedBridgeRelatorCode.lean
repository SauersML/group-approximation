import GroupApproximation.Higman.BridgeRelatorCode
import GroupApproximation.Manuscript.MFRecognition.ThreeGeneratorBridgeRecursive

/-!
# A uniform relator program for the printed two-sided bridge

This file packages the literal two-sided bridge `Bridge.BGroup` as numerical
enumerated-presentation syntax.  The generic bridge code in
`Higman.BridgeRelatorCode` concerns the one-sided auxiliary extension
`HNNEmb.Ext`; the two groups have different stable-letter relations.  We reuse
only its numerical word/certificate infrastructure and enumerate the literal
edge family from `Bridge.Effectivity.hnnFam`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace TwoSidedBridgeRelatorCode

open Nat.Partrec
open GroupApproximation.Higman
open GroupApproximation.Higman.Transport
open GroupApproximation.Higman.BridgeWP
open GroupApproximation.Higman.BridgePresentation
open GroupApproximation.EnumeratedPresentationCodes
open Bridge

namespace BRC
export GroupApproximation.Higman.BridgeRelatorCode
  (countableBaseRelator primrec_countableBaseRelator decodeCandidate
    primrec_decodeCandidate normalClosure_union_one decodeCountableInput
    primrec_decodeCountableInput rotateRaw normalizeThree primrec_rotateRaw
    primrec_normalizeThree rawToFree_normalizeThree)
end BRC

namespace Eff
export Bridge.Effectivity
  (hnnFam primrec_hnnFam codedRels extEquivCoded qC_to_coded)
end Eff

abbrev Raw : Type := RawWord
abbrev Certificate : Type := WordCertificate

/-- The canonical generating family of a standard enumerated presentation. -/
def sourceGen (c : PresentationCode) : ℕ → Carrier c :=
  fun k => PresentedGroup.of k

theorem sourceGen_spans (c : PresentationCode) :
    Subgroup.closure (Set.range (sourceGen c)) = ⊤ :=
  PresentedGroup.closure_range_of _

/-- A total enumeration of the literal countable HNN presentation.  Even
addresses enumerate certified base relations; odd addresses enumerate the
two-sided stable-letter relations and their inverses. -/
def countableRawRelator (c : PresentationCode) (address : ℕ) : Raw :=
  let p := Nat.unpair address
  if p.1 % 2 = 0 then BRC.countableBaseRelator c p.2
  else relabel cycle (Eff.hnnFam p.2)

theorem primrec_countableRawRelator :
    Primrec₂ countableRawRelator := by
  have hp : Primrec fun z : PresentationCode × ℕ => Nat.unpair z.2 :=
    Primrec.unpair.comp Primrec.snd
  have hindex : Primrec fun z : PresentationCode × ℕ =>
      (Nat.unpair z.2).2 := Primrec.snd.comp hp
  have heven : PrimrecPred fun z : PresentationCode × ℕ =>
      (Nat.unpair z.2).1 % 2 = 0 :=
    Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.fst.comp hp) (Primrec.const 2))
      (Primrec.const 0)
  have hbase : Primrec fun z : PresentationCode × ℕ =>
      BRC.countableBaseRelator z.1 (Nat.unpair z.2).2 :=
    BRC.primrec_countableBaseRelator.comp Primrec.fst hindex
  have hhnn : Primrec fun z : PresentationCode × ℕ =>
      relabel cycle (Eff.hnnFam (Nat.unpair z.2).2) :=
    (primrec_relabel primrec_cycle).comp (Eff.primrec_hnnFam.comp hindex)
  exact (Primrec.ite heven hbase hhnn).to₂

/-- The direct range of the literal countable relator enumerator. -/
def countableRelatorSet (c : PresentationCode) : Set (FreeGroup ℕ) :=
  Set.range fun address => freeEval (countableRawRelator c address)

theorem countableRelatorSet_eq (c : PresentationCode) :
    countableRelatorSet c = Eff.codedRels (sourceGen c) ∪ {1} := by
  apply Set.eq_of_subset_of_subset
  · rintro z ⟨address, rfl⟩
    let p := Nat.unpair address
    by_cases heven : p.1 % 2 = 0
    · let q := BRC.decodeCandidate p.2
      by_cases hcheck : wordCheck (c, q.1) q.2 = true
      · apply Or.inl
        have htrivial : evalRaw (sourceGen c) q.1 = 1 :=
          (wordCheck_complete c q.1).2 ⟨q.2, hcheck⟩
        refine ⟨FreeGroup.map (fun k => k + 3) (freeEval q.1),
          Or.inl ⟨freeEval q.1,
            (mem_wordSet_iff (sourceGen c) q.1).2 htrivial, rfl⟩, ?_⟩
        simp [countableRawRelator, p, heven,
          BRC.countableBaseRelator, q, hcheck, freeEval_relabel]
      · apply Or.inr
        simp [countableRawRelator, p, heven, BRC.countableBaseRelator, q,
          hcheck, freeEval]
    · apply Or.inl
      refine ⟨freeEval (Eff.hnnFam p.2), Or.inr ⟨p.2, rfl⟩, ?_⟩
      simp [countableRawRelator, p, heven, freeEval_relabel]
  · rintro z (hz | hz)
    · obtain ⟨u, hu, rfl⟩ := hz
      rcases hu with ⟨v, hv, rfl⟩ | ⟨n, rfl⟩
      · obtain ⟨w, hw⟩ :=
          (mem_closure_iff_exists_evalRaw FreeGroup.of v).1
            (by rw [FreeGroup.closure_range_of]; exact Subgroup.mem_top v)
        have hw' : freeEval w = v := hw
        have hvw : freeEval w ∈ wordSet (sourceGen c) := by
          rw [hw']
          exact hv
        obtain ⟨cert, hcert⟩ := (wordCheck_complete c w).1
          ((mem_wordSet_iff (sourceGen c) w).1 hvw)
        refine ⟨Nat.pair 0 (Encodable.encode (w, cert)), ?_⟩
        simp [countableRawRelator, BRC.countableBaseRelator,
          BRC.decodeCandidate, hcert, freeEval_relabel, hw']
      · refine ⟨Nat.pair 1 n, ?_⟩
        simp [countableRawRelator, freeEval_relabel]
    · have hzone : z = 1 := by simpa using hz
      subst z
      obtain ⟨cert, hcert⟩ := (wordCheck_complete c []).1 (by simp)
      refine ⟨Nat.pair 0 (Encodable.encode (([] : Raw), cert)), ?_⟩
      simp [countableRawRelator, BRC.countableBaseRelator,
        BRC.decodeCandidate, hcert, freeEval]

theorem normalClosure_countableRelatorSet (c : PresentationCode) :
    Subgroup.normalClosure (countableRelatorSet c) =
      Subgroup.normalClosure (Eff.codedRels (sourceGen c)) := by
  rw [countableRelatorSet_eq, BRC.normalClosure_union_one]

/-! ## Numerical packaging of the countable presentation -/

def decodeCountableInput (n : ℕ) : PresentationCode × ℕ :=
  BRC.decodeCountableInput n

theorem primrec_decodeCountableInput : Primrec decodeCountableInput :=
  BRC.primrec_decodeCountableInput

def encodedCountableEnumerator (input : ℕ) : Part ℕ :=
  let p := decodeCountableInput input
  Part.some (Encodable.encode (countableRawRelator p.1 p.2))

theorem encodedCountableEnumerator_partrec :
    Nat.Partrec encodedCountableEnumerator := by
  have hvalue : Primrec fun input : ℕ => Encodable.encode
      (countableRawRelator (decodeCountableInput input).1
        (decodeCountableInput input).2) :=
    Primrec.encode.comp
      (primrec_countableRawRelator.comp
        (Primrec.fst.comp primrec_decodeCountableInput)
        (Primrec.snd.comp primrec_decodeCountableInput))
  exact Nat.Partrec.of_primrec (Primrec.nat_iff.mp hvalue)

noncomputable def universalCountableCode : Code :=
  (Code.exists_code.mp encodedCountableEnumerator_partrec).choose

theorem eval_universalCountableCode :
    Code.eval universalCountableCode = encodedCountableEnumerator :=
  (Code.exists_code.mp encodedCountableEnumerator_partrec).choose_spec

/-- Uniform standard program for the literal countable bridge presentation. -/
noncomputable def countableCode (c : PresentationCode) : PresentationCode :=
  Code.curry universalCountableCode (Encodable.encode c)

theorem primrec_countableCode : Primrec countableCode :=
  Code.primrec₂_curry.comp
    (Primrec.const universalCountableCode) Primrec.encode

theorem computable_countableCode : Computable countableCode :=
  primrec_countableCode.to_comp

theorem eval_countableCode (c : PresentationCode) (address : ℕ) :
    Code.eval (countableCode c) address =
      Part.some (Encodable.encode (countableRawRelator c address)) := by
  rw [countableCode, Code.eval_curry, eval_universalCountableCode]
  simp [encodedCountableEnumerator, decodeCountableInput,
    BRC.decodeCountableInput]

theorem standard_countable_relatorSet_eq (c : PresentationCode) :
    relatorSet (countableCode c) = countableRelatorSet c ∪ {1} := by
  ext z
  constructor
  · rintro ⟨encodedAddress, rfl⟩
    let p := Nat.unpair encodedAddress
    cases heval : Code.evaln p.2 (countableCode c) p.1 with
    | none =>
        apply Or.inr
        simp [rawRelator, p, heval, freeEval]
    | some y =>
        have hsound : y ∈ Code.eval (countableCode c) p.1 := Code.evaln_sound heval
        rw [eval_countableCode] at hsound
        have hy : y = Encodable.encode (countableRawRelator c p.1) := by
          simpa using hsound
        apply Or.inl
        refine ⟨p.1, ?_⟩
        simp [rawRelator, decodeRawWord, p, heval, hy]
  · rintro (hz | hz)
    · obtain ⟨address, rfl⟩ := hz
      have hmem : Encodable.encode (countableRawRelator c address) ∈
          Code.eval (countableCode c) address := by
        rw [eval_countableCode]
        exact Part.mem_some _
      obtain ⟨stage, hstage⟩ := Code.evaln_complete.mp hmem
      have hstage' : Code.evaln stage (countableCode c) address =
          some (Encodable.encode (countableRawRelator c address)) := hstage
      refine ⟨Nat.pair address stage, ?_⟩
      simp [rawRelator, decodeRawWord, hstage']
    · have hzone : z = 1 := by simpa using hz
      subst z
      refine ⟨Nat.pair 0 0, ?_⟩
      have hnone : Code.evaln 0 (countableCode c) 0 = Option.none := by
        cases h : Code.evaln 0 (countableCode c) 0 with
        | none => rfl
        | some y =>
            have hlt : 0 < 0 := Code.evaln_bound h
            omega
      simp [rawRelator, hnone, freeEval]

theorem normalClosure_standard_countable (c : PresentationCode) :
    Subgroup.normalClosure (relatorSet (countableCode c)) =
      Subgroup.normalClosure (Eff.codedRels (sourceGen c)) := by
  rw [standard_countable_relatorSet_eq,
    BRC.normalClosure_union_one,
    normalClosure_countableRelatorSet]

/-! ## The exact rank-three kernel program -/

/-- Rotate the source spelling `(x,y,t)` to the literal numbered-presentation
convention `(t,x,y)`. -/
def rotateRaw (w : Raw) : Raw := BRC.rotateRaw w

/-- Normalize arbitrary natural letter codes to the three-letter alphabet. -/
def normalizeThree (w : Raw) : Raw := BRC.normalizeThree w

theorem primrec_rotateRaw : Primrec rotateRaw := BRC.primrec_rotateRaw

theorem primrec_normalizeThree : Primrec normalizeThree :=
  BRC.primrec_normalizeThree

theorem rawToFree_normalizeThree (w : Raw) :
    rawToFree 2 (normalizeThree w) = rawToFree 2 w :=
  BRC.rawToFree_normalizeThree w

/-- The literal three-generator quotient map for the bridge over the canonical
generating family of `Carrier c`. -/
noncomputable def bridgeMap (c : PresentationCode) :
    FreeGroup (Fin 3) →* Bridge.BGroup (Bridge.seq (sourceGen c)) :=
  Bridge.qC (Bridge.seq (sourceGen c))

/-- One attempted kernel relator, emitted exactly when its rotated spelling
has a word-problem certificate in the literal countable bridge presentation. -/
noncomputable def rankThreeRawRelator (c : PresentationCode)
    (address : ℕ) : Raw :=
  let q := BRC.decodeCandidate address
  bif wordCheck (countableCode c, rotateRaw q.1) q.2 then
    normalizeThree q.1
  else []

theorem primrec_rankThreeRawRelator :
    Primrec₂ rankThreeRawRelator := by
  have hq : Primrec fun z : PresentationCode × ℕ =>
      BRC.decodeCandidate z.2 := BRC.primrec_decodeCandidate.comp Primrec.snd
  have hw : Primrec fun z : PresentationCode × ℕ =>
      (BRC.decodeCandidate z.2).1 := Primrec.fst.comp hq
  have hcert : Primrec fun z : PresentationCode × ℕ =>
      (BRC.decodeCandidate z.2).2 := Primrec.snd.comp hq
  have hcode : Primrec fun z : PresentationCode × ℕ =>
      countableCode z.1 := primrec_countableCode.comp Primrec.fst
  have hrot : Primrec fun z : PresentationCode × ℕ =>
      rotateRaw (BRC.decodeCandidate z.2).1 := primrec_rotateRaw.comp hw
  have hcheck : Primrec fun z : PresentationCode × ℕ =>
      wordCheck (countableCode z.1, rotateRaw (BRC.decodeCandidate z.2).1)
        (BRC.decodeCandidate z.2).2 :=
    primrec_wordCheck.comp (Primrec.pair hcode hrot) hcert
  exact (Primrec.cond hcheck (primrec_normalizeThree.comp hw)
    (Primrec.const [])).to₂

/-- The finite-rank relator range emitted by the literal kernel program. -/
def rankThreeRelatorSet (c : PresentationCode) : Set (FreeGroup (Fin 3)) :=
  Set.range fun address => rawToFree 2 (rankThreeRawRelator c address)

theorem bridgeMap_eq_one_iff_wordCheck (c : PresentationCode) (w : Raw) :
    bridgeMap c (rawToFree 2 w) = 1 ↔
      ∃ cert : Certificate,
        wordCheck (countableCode c, rotateRaw w) cert = true := by
  rw [← (Eff.extEquivCoded (sourceGen c) (sourceGen_spans c)).map_eq_one_iff]
  change Eff.extEquivCoded (sourceGen c) (sourceGen_spans c)
      (Bridge.qC (Bridge.seq (sourceGen c)) (rawToFree 2 w)) = 1 ↔ _
  rw [Eff.qC_to_coded]
  change evalRaw
      (fun k => (PresentedGroup.of k :
        PresentedGroup (Eff.codedRels (sourceGen c))))
      (rotateRaw w) = 1 ↔ _
  rw [evalRaw_presentedGroup_eq_one_iff]
  rw [← normalClosure_standard_countable]
  rw [← evalRaw_presentedGroup_eq_one_iff]
  exact wordCheck_complete (countableCode c) (rotateRaw w)

/-- Exactness: the emitted range is the kernel of the printed bridge map. -/
theorem rankThreeRelatorSet_eq_ker (c : PresentationCode) :
    rankThreeRelatorSet c =
      (MonoidHom.ker (bridgeMap c) : Set (FreeGroup (Fin 3))) := by
  apply Set.eq_of_subset_of_subset
  · rintro z ⟨address, rfl⟩
    let q := BRC.decodeCandidate address
    by_cases hcheck :
        wordCheck (countableCode c, rotateRaw q.1) q.2 = true
    · change bridgeMap c
          (rawToFree 2 (rankThreeRawRelator c address)) = 1
      simp [rankThreeRawRelator, q, hcheck, rawToFree_normalizeThree]
      exact (bridgeMap_eq_one_iff_wordCheck c q.1).2 ⟨q.2, hcheck⟩
    · change bridgeMap c
          (rawToFree 2 (rankThreeRawRelator c address)) = 1
      simp [rankThreeRawRelator, q, hcheck, rawToFree_nil]
  · intro z hz
    obtain ⟨w, rfl⟩ := rawToFree_surjective 2 z
    obtain ⟨cert, hcert⟩ := (bridgeMap_eq_one_iff_wordCheck c w).1 hz
    refine ⟨Encodable.encode (w, cert), ?_⟩
    simp [rankThreeRawRelator, BRC.decodeCandidate, hcert,
      rawToFree_normalizeThree]

theorem normalClosure_rankThreeRelatorSet (c : PresentationCode) :
    Subgroup.normalClosure (rankThreeRelatorSet c) =
      MonoidHom.ker (bridgeMap c) := by
  rw [rankThreeRelatorSet_eq_ker]
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (fun _ h => h)
  · exact Subgroup.subset_normalClosure

/-- The group presented by the numerical rank-three kernel is the literal
two-sided bridge itself. -/
noncomputable def rankThreePresentedEquiv (c : PresentationCode) :
    PresentedGroup (rankThreeRelatorSet c) ≃*
      Bridge.BGroup (Bridge.seq (sourceGen c)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (normalClosure_rankThreeRelatorSet c)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (bridgeMap c)
      (Bridge.qC_surjective _
        (Bridge.closure_range_seq (sourceGen c) (sourceGen_spans c))))

@[simp] theorem rankThreePresentedEquiv_of (c : PresentationCode) (j : Fin 3) :
    rankThreePresentedEquiv c (PresentedGroup.of j) =
      Bridge.gen3 (Bridge.seq (sourceGen c)) j := by
  show QuotientGroup.quotientKerEquivOfSurjective
      (bridgeMap c)
      (Bridge.qC_surjective _
        (Bridge.closure_range_seq (sourceGen c) (sourceGen_spans c)))
      (QuotientGroup.quotientMulEquivOfEq
        (normalClosure_rankThreeRelatorSet c)
        (PresentedGroup.of j)) = _
  rw [show QuotientGroup.quotientMulEquivOfEq
      (normalClosure_rankThreeRelatorSet c) (PresentedGroup.of j) =
        (QuotientGroup.mk (FreeGroup.of j) :
          FreeGroup (Fin 3) ⧸ MonoidHom.ker (bridgeMap c)) from rfl]
  rw [show QuotientGroup.quotientKerEquivOfSurjective
      (bridgeMap c)
      (Bridge.qC_surjective _
        (Bridge.closure_range_seq (sourceGen c) (sourceGen_spans c)))
      (QuotientGroup.mk (FreeGroup.of j) :
        FreeGroup (Fin 3) ⧸ MonoidHom.ker (bridgeMap c)) =
        bridgeMap c (FreeGroup.of j) from rfl]
  exact FreeGroup.lift_apply_of

/-! ## Numerical packaging of the rank-three program -/

def decodeRankThreeInput (n : ℕ) : PresentationCode × ℕ :=
  decodeCountableInput n

noncomputable def encodedRankThreeEnumerator (input : ℕ) : Part ℕ :=
  let p := decodeRankThreeInput input
  Part.some (Encodable.encode (rankThreeRawRelator p.1 p.2))

theorem encodedRankThreeEnumerator_partrec :
    Nat.Partrec encodedRankThreeEnumerator := by
  have hvalue : Primrec fun input : ℕ => Encodable.encode
      (rankThreeRawRelator (decodeRankThreeInput input).1
        (decodeRankThreeInput input).2) :=
    Primrec.encode.comp
      (primrec_rankThreeRawRelator.comp
        (Primrec.fst.comp primrec_decodeCountableInput)
        (Primrec.snd.comp primrec_decodeCountableInput))
  exact Nat.Partrec.of_primrec (Primrec.nat_iff.mp hvalue)

noncomputable def universalRankThreeCode : Code :=
  (Code.exists_code.mp encodedRankThreeEnumerator_partrec).choose

theorem eval_universalRankThreeCode :
    Code.eval universalRankThreeCode = encodedRankThreeEnumerator :=
  (Code.exists_code.mp encodedRankThreeEnumerator_partrec).choose_spec

/-- A numerical program enumerating exactly the literal rank-three bridge
kernel. -/
noncomputable def rankThreeCode (c : PresentationCode) : Code :=
  Code.curry universalRankThreeCode (Encodable.encode c)

theorem primrec_rankThreeCode : Primrec rankThreeCode :=
  Code.primrec₂_curry.comp
    (Primrec.const universalRankThreeCode) Primrec.encode

theorem computable_rankThreeCode : Computable rankThreeCode :=
  primrec_rankThreeCode.to_comp

theorem eval_rankThreeCode (c : PresentationCode) (address : ℕ) :
    Code.eval (rankThreeCode c) address =
      Part.some (Encodable.encode (rankThreeRawRelator c address)) := by
  rw [rankThreeCode, Code.eval_curry, eval_universalRankThreeCode]
  simp [encodedRankThreeEnumerator, decodeRankThreeInput,
    decodeCountableInput, BRC.decodeCountableInput]

end TwoSidedBridgeRelatorCode
end MFRecognition
end Manuscript
end GroupApproximation
