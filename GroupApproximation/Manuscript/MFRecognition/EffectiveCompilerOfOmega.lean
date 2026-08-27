import GroupApproximation.Computability.BooneWordMapPrimrec
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Computability.RawWord
import GroupApproximation.Computability.AdianRabinWordProblem
import GroupApproximation.Higman.BridgePresentation
import GroupApproximation.Higman.CurrentREBenign
import GroupApproximation.Higman.RelabelPresentation
import GroupApproximation.Manuscript.MFRecognition.EffectiveHigmanCompiler
import GroupApproximation.Manuscript.MFRecognition.FixedUniversalFamily
import GroupApproximation.Manuscript.MFRecognition.FixedUniversalHostCompiler

/-!
# The effective Higman compiler, from the ω-closure

`EffectiveHigmanCompiler` asks for a computable map from a recursive
presentation code on `x, y, t` to a finite presentation code together with
three marked words inducing an embedding.  The input codes are
`Nat.Partrec.Code`, so they are enumerated by naturals, and the whole family
of inputs can be handled at once:

* `allQcode n` is the `n`-th recursive presentation code, so `allQcode` runs
  over *every* rank-three input, and `allQcode (encode P) = P`;
* the free product of all `PresentedQ (allQcode n)`, with the `n`-th alphabet
  in the block `3n, 3n+1, 3n+2`, is one recursively presented group
  (`recursivePresentationUniversal`);
* the effective three-generator bridge and Higman's embedding theorem — the
  latter available from `hOmega` through `fpOvergroup_of_fgRecursive_of_omega`
  — put that group inside one finitely presented host, coded once by
  `exists_code_mulEquiv`;
* the images of the block generators are spelled by the bridge words at
  indices `3n`, `3n+1`, `3n+2`, which are computable in `n`.

So the host code is a constant and only the three words vary, which is
exactly `FixedUniversalHostCompiler allQcode`.  Composing with
`Encodable.encode` turns the index-indexed compiler into one defined at every
code, and the compiler debt reduces to the ω-debt.

This is the same construction as `FixedUniversalHostOfOmega`, which runs it
for the auxiliary one-sided family `TwoSidedConcreteQCodeFamily.indexedQcode`;
here the family is the tautological enumeration of all codes, so nothing about
the manuscript's `qcodeSeed` has to be checked.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace EffectiveCompilerOfOmega

noncomputable section

/-! ## The tautological family of every rank-three input -/

/-- Enumerate every recursive presentation code by naturals. -/
def allQcode (n : ℕ) : RecPresCode := Denumerable.ofNat Nat.Partrec.Code n

theorem primrec_allQcode : Primrec allQcode :=
  Primrec.ofNat Nat.Partrec.Code

theorem computable_allQcode : Computable allQcode :=
  primrec_allQcode.to_comp

/-- Every code occurs in the family, at its own numerical index. -/
theorem allQcode_encode (P : RecPresCode) :
    allQcode (Encodable.encode P) = P := by
  simp [allQcode]

/-! ## A recursive presentation of the universal free product -/

section RecursiveSide

open Nat.Partrec
open Higman
open EnumeratedPresentationCodes

/-- Put a numbered letter into the `e`-th three-letter block. -/
def blockIndex (e i : ℕ) : ℕ := 3 * e + i % 3

theorem primrec_blockIndex : Primrec₂ blockIndex := by
  exact (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst)
    (Primrec.nat_mod.comp Primrec.snd (Primrec.const 3))).to₂

/-- A relator of the `e`-th input, moved into its disjoint block. -/
def universalRawRelator (address : ℕ) : RawWord :=
  let p := Nat.unpair address
  relabel (blockIndex p.1) (rawRelator (allQcode p.1) p.2)

theorem primrec_universalRawRelator : Primrec universalRawRelator := by
  have hp : Primrec fun address : ℕ => Nat.unpair address := Primrec.unpair
  have he : Primrec fun address : ℕ => (Nat.unpair address).1 :=
    Primrec.fst.comp hp
  have ha : Primrec fun address : ℕ => (Nat.unpair address).2 :=
    Primrec.snd.comp hp
  have hrel : Primrec fun address : ℕ =>
      rawRelator (allQcode (Nat.unpair address).1)
        (Nat.unpair address).2 :=
    primrec_rawRelator.comp (primrec_allQcode.comp he) ha
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
    universalRelatorSet = FixedUniversalFamily.relators allQcode := by
  ext z
  constructor
  · rintro ⟨address, rfl⟩
    rcases hpair : Nat.unpair address with ⟨e, a⟩
    change freeEval (universalRawRelator address) ∈ _
    simp only [universalRawRelator, hpair]
    rw [freeEval_blockRelabel]
    refine ⟨FreeGroup.map (CoprodIPresentation.blockInj e)
        (rank3Word (rawRelator (allQcode e) a)), ?_, ?_⟩
    · exact CoprodIPresentation.mem_coprodRels
        (fun e => rank3Relators (allQcode e))
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
        (rank3Word (rawRelator (allQcode e) a))) hhom)
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
      (rank3Word (rawRelator (allQcode e) address))) hhom).symm

/-! ### The total enumerator as one standard program -/

/-- The universal relator enumerator, as a partial function on codes. -/
def encodedUniversalEnumerator (address : ℕ) : Part ℕ :=
  Part.some (Encodable.encode (universalRawRelator address))

theorem encodedUniversalEnumerator_partrec :
    Nat.Partrec encodedUniversalEnumerator :=
  Nat.Partrec.of_primrec
    (Primrec.nat_iff.mp (Primrec.encode.comp primrec_universalRawRelator))

/-- One numerical program enumerating all relators of the universal free
product. -/
def universalCode : Code :=
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
      Subgroup.normalClosure (FixedUniversalFamily.relators allQcode) := by
  rw [standardRelatorSet_eq, universalRelatorSet_eq, normalClosure_union_one]

/-- The standard coded carrier is the fixed universal free product. -/
def carrierEquivUniversal :
    Carrier universalCode ≃* FixedUniversalFamily.U allQcode :=
  QuotientGroup.quotientMulEquivOfEq normalClosure_standardRelatorSet

@[simp] theorem carrierEquivUniversal_of (n : ℕ) :
    carrierEquivUniversal (PresentedGroup.of n : Carrier universalCode) =
      (PresentedGroup.of n : FixedUniversalFamily.U allQcode) := rfl

/-- The universal free product is recursively presented, transported from the
literal standard code. -/
def recursivePresentationUniversal :
    RecursivePresentation (FixedUniversalFamily.U allQcode) where
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

end RecursiveSide

/-! ## One fixed marked host for the whole family -/

section HostSide

open Higman
open PresentationCodes

/-- The free product of every rank-three input. -/
abbrev Universal : Type := FixedUniversalFamily.U allQcode

/-- Its recursive presentation on the standard countable alphabet. -/
def universalPresentation : RecursivePresentation Universal :=
  recursivePresentationUniversal

/-- The once-only three-generator bridge of the universal family. -/
abbrev UniversalBridge : Type :=
  HNNEmb.Ext universalPresentation.gen

/-- The bridge is finitely generated and recursively presented. -/
def universalBridgeRecursive : FGRecursive UniversalBridge :=
  (BridgePresentation.bridgeEffective.recursive Universal
    universalPresentation.gen universalPresentation.spans
    universalPresentation.re).some

/-- One finitely presented overgroup of the once-only bridge. -/
def universalFPOvergroup (hOmega : Omega.OmegaInput) :
    FPOvergroup UniversalBridge :=
  (fpOvergroup_of_fgRecursive_of_omega hOmega universalBridgeRecursive).some

/-- A single numerical finite presentation for the fixed host. -/
def hostCode (hOmega : Omega.OmegaInput) : PresentationCode :=
  (exists_code_mulEquiv (universalFPOvergroup hOmega).K).choose

/-- The coded host presents the finitely presented overgroup chosen above. -/
def hostEquiv (hOmega : Omega.OmegaInput) :
    Host (hostCode hOmega) ≃* (universalFPOvergroup hOmega).K :=
  (exists_code_mulEquiv (universalFPOvergroup hOmega).K).choose_spec.some

/-- The once-only bridge embeds in the coded host. -/
def bridgeHostEmb (hOmega : Omega.OmegaInput) :
    UniversalBridge →* Host (hostCode hOmega) :=
  (hostEquiv hOmega).symm.toMonoidHom.comp
    (universalFPOvergroup hOmega).emb

theorem bridgeHostEmb_injective (hOmega : Omega.OmegaInput) :
    Function.Injective (bridgeHostEmb hOmega) :=
  (hostEquiv hOmega).symm.injective.comp
    (universalFPOvergroup hOmega).emb_injective

/-- The universal free product embeds through its base copy in the bridge. -/
def universalHostEmb (hOmega : Omega.OmegaInput) :
    Universal →* Host (hostCode hOmega) :=
  (bridgeHostEmb hOmega).comp (HNNEmb.embA universalPresentation.gen)

theorem universalHostEmb_injective (hOmega : Omega.OmegaInput) :
    Function.Injective (universalHostEmb hOmega) :=
  (bridgeHostEmb_injective hOmega).comp
    (HNNEmb.embA_injective universalPresentation.gen)

/-! ### Raw representatives and the varying bridge words -/

/-- Evaluate a raw word in the fixed host. -/
def hostRawEval (hOmega : Omega.OmegaInput) (w : RawWord) :
    Host (hostCode hOmega) :=
  hostQuotient (hostCode hOmega) (wordOf (hostCode hOmega) w)

theorem hostRawEval_surjective (hOmega : Omega.OmegaInput) :
    Function.Surjective (hostRawEval hOmega) :=
  (PresentedGroup.mk_surjective (hostRelators (hostCode hOmega))).comp
    (AdianRabinWordProblem.wordOf_surjective (hostCode hOmega))

/-- A raw spelling of a host element. -/
def rawOf (hOmega : Omega.OmegaInput) (g : Host (hostCode hOmega)) : RawWord :=
  Function.surjInv (hostRawEval_surjective hOmega) g

@[simp] theorem hostRawEval_rawOf (hOmega : Omega.OmegaInput)
    (g : Host (hostCode hOmega)) : hostRawEval hOmega (rawOf hOmega g) = g :=
  Function.surjInv_eq (hostRawEval_surjective hOmega) g

/-- A host spelling of the first bridge generator. -/
def rawX (hOmega : Omega.OmegaInput) : RawWord :=
  rawOf hOmega (bridgeHostEmb hOmega
    (BridgeEff.gen3 universalPresentation.gen 0))

/-- A host spelling of the second bridge generator. -/
def rawY (hOmega : Omega.OmegaInput) : RawWord :=
  rawOf hOmega (bridgeHostEmb hOmega
    (BridgeEff.gen3 universalPresentation.gen 1))

/-- A host spelling of the stable bridge letter. -/
def rawT (hOmega : Omega.OmegaInput) : RawWord :=
  rawOf hOmega (bridgeHostEmb hOmega
    (BridgeEff.gen3 universalPresentation.gen 2))

/-- Concatenate a fixed raw word `n` times. -/
def repeatRaw (w : RawWord) : ℕ → RawWord
  | 0 => []
  | n + 1 => w ++ repeatRaw w n

theorem primrec_repeatRaw (w : RawWord) : Primrec (repeatRaw w) := by
  have h : Primrec (Nat.rec ([] : RawWord)
      (fun _ ih => w ++ ih) : ℕ → RawWord) :=
    Primrec.nat_rec₁ _
      (Primrec.list_append.comp (Primrec.const w) Primrec.snd).to₂
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatRaw, Nat.rec_add_one, ih]

/-- The raw spelling of `x^{-n} y x^n` after substituting fixed host words. -/
def conjugateRaw (rx ry : RawWord) (n : ℕ) : RawWord :=
  repeatRaw (RawWord.invWord rx) n ++ ry ++ repeatRaw rx n

/-- The raw spelling of the universal bridge word at index `n`. -/
def markedBridgeRaw (rx ry rt : RawWord) (n : ℕ) : RawWord :=
  rt ++ conjugateRaw rx ry n ++ RawWord.invWord rt ++
    RawWord.invWord (conjugateRaw rx ry n)

theorem primrec_conjugateRaw (rx ry : RawWord) :
    Primrec (conjugateRaw rx ry) := by
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (primrec_repeatRaw (RawWord.invWord rx)) (Primrec.const ry))
    (primrec_repeatRaw rx)

theorem primrec_markedBridgeRaw (rx ry rt : RawWord) :
    Primrec (markedBridgeRaw rx ry rt) := by
  have hc := primrec_conjugateRaw rx ry
  have hleft : Primrec fun n => rt ++ conjugateRaw rx ry n :=
    Primrec.list_append.comp (Primrec.const rt) hc
  have hmiddle : Primrec fun n =>
      rt ++ conjugateRaw rx ry n ++ RawWord.invWord rt :=
    Primrec.list_append.comp hleft (Primrec.const (RawWord.invWord rt))
  exact Primrec.list_append.comp hmiddle
    (Computability.primrec_invWord.comp hc)

theorem wordOf_repeatRaw (c : PresentationCode) (w : RawWord) (n : ℕ) :
    wordOf c (repeatRaw w n) = (wordOf c w) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [repeatRaw, RawWord.wordOf_append, ih, pow_succ']

theorem hostRawEval_markedBridgeRaw (hOmega : Omega.OmegaInput) (n : ℕ) :
    hostRawEval hOmega
        (markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega) n) =
      bridgeHostEmb hOmega
        (BridgeEff.pi3 universalPresentation.gen
          (BridgeEff.bridgeFree n)) := by
  have hx := hostRawEval_rawOf hOmega
    (bridgeHostEmb hOmega (BridgeEff.gen3 universalPresentation.gen 0))
  have hy := hostRawEval_rawOf hOmega
    (bridgeHostEmb hOmega (BridgeEff.gen3 universalPresentation.gen 1))
  have ht := hostRawEval_rawOf hOmega
    (bridgeHostEmb hOmega (BridgeEff.gen3 universalPresentation.gen 2))
  simp only [hostRawEval, markedBridgeRaw, conjugateRaw,
    RawWord.wordOf_append, RawWord.wordOf_invWord, wordOf_repeatRaw,
    map_mul, map_inv, map_pow] at hx hy ht ⊢
  unfold rawX rawY rawT
  rw [hx, hy, ht]
  simp only [BridgeEff.bridgeFree, map_mul, map_inv, map_zpow,
    BridgeEff.pi3_zero, BridgeEff.pi3_one, BridgeEff.pi3_two,
    BridgeEff.gen3_zero, BridgeEff.gen3_one, BridgeEff.gen3_two]
  group

/-- The first marked word for input `e`. -/
def wordX (hOmega : Omega.OmegaInput) (e : ℕ) : RawWord :=
  markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega) (3 * e)

/-- The second marked word for input `e`. -/
def wordY (hOmega : Omega.OmegaInput) (e : ℕ) : RawWord :=
  markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega) (3 * e + 1)

/-- The third marked word for input `e`. -/
def wordT (hOmega : Omega.OmegaInput) (e : ℕ) : RawWord :=
  markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega) (3 * e + 2)

theorem computable_wordX (hOmega : Omega.OmegaInput) :
    Computable (wordX hOmega) :=
  (primrec_markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega)).to_comp.comp
    (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id).to_comp

theorem computable_wordY (hOmega : Omega.OmegaInput) :
    Computable (wordY hOmega) :=
  (primrec_markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega)).to_comp.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
      (Primrec.const 1)).to_comp

theorem computable_wordT (hOmega : Omega.OmegaInput) :
    Computable (wordT hOmega) :=
  (primrec_markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega)).to_comp.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
      (Primrec.const 2)).to_comp

/-! ### The fixed-host compiler on the tautological family -/

/-- One host, one embedding, and three computable words per index: the
fixed-universal-host compiler for the family of all rank-three codes. -/
def compiler (hOmega : Omega.OmegaInput) :
    FixedUniversalHostCompiler allQcode where
  U := Universal
  host := hostCode hOmega
  hostEmb := universalHostEmb hOmega
  hostEmb_injective := universalHostEmb_injective hOmega
  wordX := wordX hOmega
  wordY := wordY hOmega
  wordT := wordT hOmega
  computable_wordX := computable_wordX hOmega
  computable_wordY := computable_wordY hOmega
  computable_wordT := computable_wordT hOmega
  sourceEmb := FixedUniversalFamily.sourceEmb allQcode
  sourceEmb_injective := FixedUniversalFamily.sourceEmb_injective allQcode
  marked_comm := by
    intro e
    apply FreeGroup.ext_hom
    intro i
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, markedHom_apply_of]
    fin_cases i
    · change hostRawEval hOmega (wordX hOmega e) = _
      unfold wordX
      rw [hostRawEval_markedBridgeRaw, BridgeEff.pi3_bridgeFree]
      apply congrArg (bridgeHostEmb hOmega)
      apply congrArg (HNNEmb.embA universalPresentation.gen)
      change carrierEquivUniversal (PresentedGroup.of (3 * e)) =
        FixedUniversalFamily.sourceEmb allQcode e
          (PresentedGroup.of (0 : Fin 3))
      rw [carrierEquivUniversal_of, FixedUniversalFamily.sourceEmb_of]
      congr 1
    · change hostRawEval hOmega (wordY hOmega e) = _
      unfold wordY
      rw [hostRawEval_markedBridgeRaw, BridgeEff.pi3_bridgeFree]
      apply congrArg (bridgeHostEmb hOmega)
      apply congrArg (HNNEmb.embA universalPresentation.gen)
      change carrierEquivUniversal (PresentedGroup.of (3 * e + 1)) =
        FixedUniversalFamily.sourceEmb allQcode e
          (PresentedGroup.of (1 : Fin 3))
      rw [carrierEquivUniversal_of, FixedUniversalFamily.sourceEmb_of]
      congr 1
    · change hostRawEval hOmega (wordT hOmega e) = _
      unfold wordT
      rw [hostRawEval_markedBridgeRaw, BridgeEff.pi3_bridgeFree]
      apply congrArg (bridgeHostEmb hOmega)
      apply congrArg (HNNEmb.embA universalPresentation.gen)
      change carrierEquivUniversal (PresentedGroup.of (3 * e + 2)) =
        FixedUniversalFamily.sourceEmb allQcode e
          (PresentedGroup.of (2 : Fin 3))
      rw [carrierEquivUniversal_of, FixedUniversalFamily.sourceEmb_of]
      congr 1

end HostSide

/-! ## The compiler at every rank-three code -/

/-- Move a marked output along an equality of input codes. -/
def transportOutput {P Q : RecPresCode} (h : P = Q)
    (o : MarkedHigmanOutput P) : MarkedHigmanOutput Q := h ▸ o

@[simp] theorem transportOutput_raw {P Q : RecPresCode} (h : P = Q)
    (o : MarkedHigmanOutput P) : (transportOutput h o).raw = o.raw := by
  cases h
  rfl

/-- The compiler on every rank-three code: run the fixed-host compiler at the
numerical index of the code. -/
def rawCompile (hOmega : Higman.Omega.OmegaInput) (P : RecPresCode) :
    RawMarkedOutput :=
  (compiler hOmega).compile (Encodable.encode P)

theorem computable_rawCompile (hOmega : Higman.Omega.OmegaInput) :
    Computable (rawCompile hOmega) :=
  (compiler hOmega).computable_compile.comp Computable.encode

theorem rawCompile_marks (hOmega : Higman.Omega.OmegaInput) (P : RecPresCode) :
    (transportOutput (allQcode_encode P)
        ((compiler hOmega).output (Encodable.encode P))).raw =
      rawCompile hOmega P := by
  rw [transportOutput_raw]
  exact (compiler hOmega).output_raw (Encodable.encode P)

/-- **The effective Higman compiler, built from the ω-closure.** -/
def effectiveCompiler (hOmega : Higman.Omega.OmegaInput) :
    EffectiveHigmanCompiler where
  compile := rawCompile hOmega
  computable := computable_rawCompile hOmega
  marks := fun P =>
    ⟨transportOutput (allQcode_encode P)
        ((compiler hOmega).output (Encodable.encode P)),
      rawCompile_marks hOmega P⟩

/-- **The compiler debt reduces to the ω-debt.**  Higman's ω-closure gives an
effective, marked Higman compiler on every rank-three recursive presentation
code, so in particular on the manuscript's family `e ↦ Q_e`. -/
theorem effectiveHigmanCompiler_of_omega (hOmega : Higman.Omega.OmegaInput) :
    Nonempty EffectiveHigmanCompiler :=
  ⟨effectiveCompiler hOmega⟩

end

end EffectiveCompilerOfOmega
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
