import GroupApproximation.Higman.RelabelPresentation
import GroupApproximation.Manuscript.MFRecognition.ConcreteQCodeFamily

/-!
# A recursive presentation of the fixed universal family

The fixed universal group is the free product of the concrete rank-three
inputs, with the `e`-th alphabet placed in the block
`3 * e, 3 * e + 1, 3 * e + 2`.  This file supplies one numerical relator
program for that presentation.  It is the effectivity input needed to apply
the HNN bridge and Higman's embedding theorem only once.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace FixedUniversalFamilyRecursive

open Nat.Partrec
open Higman
open EnumeratedPresentationCodes
open ConcreteQCodeFamily

noncomputable section

/-- Put a numbered letter into the `e`-th three-letter block. -/
def blockIndex (e i : ℕ) : ℕ := 3 * e + i % 3

theorem primrec_blockIndex : Primrec₂ blockIndex := by
  exact (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst)
    (Primrec.nat_mod.comp Primrec.snd (Primrec.const 3))).to₂

/-- A relator of the `e`-th input, moved into its disjoint block. -/
def universalRawRelator (address : ℕ) : RawWord :=
  let p := Nat.unpair address
  relabel (blockIndex p.1) (rawRelator (indexedQcode p.1) p.2)

theorem primrec_indexedQcode : Primrec indexedQcode := by
  have hswitch : Primrec RecursiveSwitchPresentation.switchEnumeratorCode :=
    Code.primrec₂_curry.comp
      (Primrec.const RecursiveSwitchPresentation.universalSwitchEnumeratorCode)
      Primrec.encode
  exact Higman.BridgeRelatorCode.primrec_rankThreeCode.comp
    (hswitch.comp (Primrec.ofNat Code))

theorem primrec_universalRawRelator : Primrec universalRawRelator := by
  have hp : Primrec fun address : ℕ => Nat.unpair address := Primrec.unpair
  have he : Primrec fun address : ℕ => (Nat.unpair address).1 :=
    Primrec.fst.comp hp
  have ha : Primrec fun address : ℕ => (Nat.unpair address).2 :=
    Primrec.snd.comp hp
  have hrel : Primrec fun address : ℕ =>
      rawRelator (indexedQcode (Nat.unpair address).1)
        (Nat.unpair address).2 :=
    primrec_rawRelator.comp (primrec_indexedQcode.comp he) ha
  have hletter : Primrec fun z : ℕ × (ℕ × Bool) =>
      (blockIndex (Nat.unpair z.1).1 z.2.1, z.2.2) :=
    Primrec.pair
      (primrec_blockIndex.comp
        (he.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hmap : Primrec fun z : ℕ × RawWord =>
      relabel (blockIndex (Nat.unpair z.1).1) z.2 :=
    (Primrec.list_map Primrec.snd
      (hletter.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
        fun _ => rfl
  exact hmap.comp (Primrec.pair Primrec.id hrel)

/-- The direct range of the universal enumerator. -/
def universalRelatorSet : Set (FreeGroup ℕ) :=
  Set.range fun address => freeEval (universalRawRelator address)

/-- Relabelling a three-letter raw word into a numbered block agrees with
the corresponding free-group map. -/
theorem freeEval_blockRelabel (e : ℕ) (w : RawWord) :
    freeEval (relabel (blockIndex e) w) =
      FreeGroup.map (fun i : Fin 3 => 3 * e + i) (rank3Word w) := by
  rw [freeEval_relabel]
  unfold freeEval
  rw [map_evalRaw]
  simp only [FreeGroup.map.of]
  have hmap : FreeGroup.map (fun i : Fin 3 => 3 * e + i) =
      FreeGroup.lift (fun i : Fin 3 => FreeGroup.of (3 * e + i)) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.map.of, FreeGroup.lift_apply_of]
  rw [hmap]
  unfold rank3Word
  rw [BridgeWP.lift_rawToFree]
  congr 2

/-- The direct enumerator has exactly the relators of the fixed indexed free
product presentation. -/
theorem universalRelatorSet_eq :
    universalRelatorSet = FixedUniversalFamily.relators indexedQcode := by
  ext z
  constructor
  · rintro ⟨address, rfl⟩
    rcases hpair : Nat.unpair address with ⟨e, a⟩
    change freeEval (universalRawRelator address) ∈ _
    simp only [universalRawRelator, hpair]
    rw [freeEval_blockRelabel]
    refine ⟨FreeGroup.map (CoprodIPresentation.blockInj e)
        (rank3Word (rawRelator (indexedQcode e) a)), ?_, ?_⟩
    · exact CoprodIPresentation.mem_coprodRels
        (fun e => rank3Relators (indexedQcode e))
        ⟨a, rfl⟩
    · unfold PresentedGroupRelabel.relabel
      have hhom : (FreeGroup.map FixedUniversalFamily.blockEquiv).comp
          (FreeGroup.map (CoprodIPresentation.blockInj e)) =
        FreeGroup.map (fun i : Fin 3 => 3 * e + i) := by
        apply FreeGroup.ext_hom
        intro i
        simp only [MonoidHom.comp_apply, FreeGroup.map.of]
        rfl
      exact (congrArg (fun h => h
        (rank3Word (rawRelator (indexedQcode e) a))) hhom)
  · rintro ⟨s, hs, rfl⟩
    unfold FixedUniversalFamily.sigmaRelators at hs
    simp only [CoprodIPresentation.coprodRels, Set.mem_iUnion,
      Set.mem_image] at hs
    obtain ⟨e, r, hr, rfl⟩ := hs
    obtain ⟨address, rfl⟩ := hr
    refine ⟨Nat.pair e address, ?_⟩
    simp only [universalRawRelator, Nat.unpair_pair]
    rw [freeEval_blockRelabel]
    unfold PresentedGroupRelabel.relabel
    have hhom : (FreeGroup.map FixedUniversalFamily.blockEquiv).comp
        (FreeGroup.map (CoprodIPresentation.blockInj e)) =
        FreeGroup.map (fun i : Fin 3 => 3 * e + i) := by
      apply FreeGroup.ext_hom
      intro i
      simp only [MonoidHom.comp_apply, FreeGroup.map.of]
      rfl
    exact (congrArg (fun h => h
      (rank3Word (rawRelator (indexedQcode e) address))) hhom).symm

/-! ## Package the total enumerator as one standard program -/

def encodedUniversalEnumerator (address : ℕ) : Part ℕ :=
  Part.some (Encodable.encode (universalRawRelator address))

theorem encodedUniversalEnumerator_partrec :
    Nat.Partrec encodedUniversalEnumerator :=
  Nat.Partrec.of_primrec
    (Primrec.nat_iff.mp (Primrec.encode.comp primrec_universalRawRelator))

noncomputable def universalCode : Code :=
  (Code.exists_code.mp encodedUniversalEnumerator_partrec).choose

theorem eval_universalCode :
    Code.eval universalCode = encodedUniversalEnumerator :=
  (Code.exists_code.mp encodedUniversalEnumerator_partrec).choose_spec

theorem eval_universalCode_apply (address : ℕ) :
    Code.eval universalCode address =
      Part.some (Encodable.encode (universalRawRelator address)) := by
  rw [eval_universalCode]
  rfl

/-- The standard staged decoder adds only the identity relator. -/
theorem standardRelatorSet_eq :
    relatorSet universalCode = universalRelatorSet ∪ {1} := by
  ext z
  constructor
  · rintro ⟨encodedAddress, rfl⟩
    let p := Nat.unpair encodedAddress
    cases heval : Code.evaln p.2 universalCode p.1 with
    | none =>
        apply Or.inr
        simp [rawRelator, p, heval, freeEval]
    | some y =>
        have hsound : y ∈ Code.eval universalCode p.1 :=
          Code.evaln_sound heval
        rw [eval_universalCode_apply] at hsound
        have hy : y = Encodable.encode (universalRawRelator p.1) := by
          simpa using hsound
        apply Or.inl
        refine ⟨p.1, ?_⟩
        simp [rawRelator, decodeRawWord, p, heval, hy]
  · rintro (hz | hz)
    · obtain ⟨address, rfl⟩ := hz
      have hmem : Encodable.encode (universalRawRelator address) ∈
          Code.eval universalCode address := by
        rw [eval_universalCode_apply]
        exact Part.mem_some _
      obtain ⟨stage, hstage⟩ := Code.evaln_complete.mp hmem
      have hstage' : Code.evaln stage universalCode address =
          some (Encodable.encode (universalRawRelator address)) := hstage
      refine ⟨Nat.pair address stage, ?_⟩
      simp [rawRelator, decodeRawWord, hstage']
    · have hzone : z = 1 := by simpa using hz
      subst z
      refine ⟨Nat.pair 0 0, ?_⟩
      have hnone : Code.evaln 0 universalCode 0 = Option.none := by
        cases h : Code.evaln 0 universalCode 0 with
        | none => rfl
        | some y =>
            have hlt : 0 < 0 := Code.evaln_bound h
            omega
      simp [rawRelator, hnone, freeEval]

private theorem normalClosure_union_one (S : Set (FreeGroup ℕ)) :
    Subgroup.normalClosure (S ∪ {1}) = Subgroup.normalClosure S := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x (hx | hx)
    · exact Subgroup.subset_normalClosure hx
    · have : x = 1 := by simpa using hx
      subst x
      exact Subgroup.one_mem _
  · exact Subgroup.normalClosure_mono Set.subset_union_left

theorem normalClosure_standardRelatorSet :
    Subgroup.normalClosure (relatorSet universalCode) =
      Subgroup.normalClosure
        (FixedUniversalFamily.relators indexedQcode) := by
  rw [standardRelatorSet_eq, universalRelatorSet_eq, normalClosure_union_one]

/-- The standard coded carrier is the fixed universal free product. -/
def carrierEquivUniversal :
    Carrier universalCode ≃* FixedUniversalFamily.U indexedQcode :=
  QuotientGroup.quotientMulEquivOfEq normalClosure_standardRelatorSet

@[simp] theorem carrierEquivUniversal_of (n : ℕ) :
    carrierEquivUniversal (PresentedGroup.of n : Carrier universalCode) =
      (PresentedGroup.of n : FixedUniversalFamily.U indexedQcode) := rfl

/-- The fixed universal family is recursively presented, transported from
the literal standard code. -/
def recursivePresentationUniversal :
    RecursivePresentation (FixedUniversalFamily.U indexedQcode) where
  gen n := carrierEquivUniversal
    (PresentedGroup.of n : Carrier universalCode)
  spans := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := carrierEquivUniversal.surjective x
    have hy : y ∈ Subgroup.closure
        (Set.range fun n => (PresentedGroup.of n : Carrier universalCode)) := by
      rw [PresentedGroup.closure_range_of]
      exact Subgroup.mem_top y
    exact Subgroup.closure_induction
      (p := fun y _ => carrierEquivUniversal y ∈
        Subgroup.closure (Set.range fun n => carrierEquivUniversal
          (PresentedGroup.of n : Carrier universalCode)))
      (by
        rintro _ ⟨n, rfl⟩
        exact Subgroup.subset_closure ⟨n, rfl⟩)
      (by simp)
      (fun _ _ _ _ ha hb => by
        rw [map_mul]
        exact Subgroup.mul_mem _ ha hb)
      (fun _ _ ha => by
        rw [map_inv]
        exact Subgroup.inv_mem _ ha)
      hy
  re := by
    have hre := (recursivePresentation universalCode).re
    exact hre.of_eq fun w => by
      change evalRaw
        (fun n => (PresentedGroup.of n : Carrier universalCode)) w = 1 ↔
          evalRaw (fun n => carrierEquivUniversal
            (PresentedGroup.of n : Carrier universalCode)) w = 1
      constructor
      · intro hw
        calc
          evalRaw (fun n => carrierEquivUniversal
              (PresentedGroup.of n : Carrier universalCode)) w =
              carrierEquivUniversal
                (evalRaw (fun n =>
                  (PresentedGroup.of n : Carrier universalCode)) w) :=
            (map_evalRaw carrierEquivUniversal.toMonoidHom _ w).symm
          _ = 1 := by rw [hw, map_one]
      · intro hw
        apply carrierEquivUniversal.injective
        calc
          carrierEquivUniversal
              (evalRaw (fun n =>
                (PresentedGroup.of n : Carrier universalCode)) w) =
              evalRaw (fun n => carrierEquivUniversal
                (PresentedGroup.of n : Carrier universalCode)) w :=
            map_evalRaw carrierEquivUniversal.toMonoidHom _ w
          _ = 1 := hw
          _ = carrierEquivUniversal 1 := map_one _ |>.symm

end

end FixedUniversalFamilyRecursive
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
