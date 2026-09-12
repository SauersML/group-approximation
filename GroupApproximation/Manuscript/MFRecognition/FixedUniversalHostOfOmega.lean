import GroupApproximation.Computability.BooneWordMapPrimrec
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Computability.RawWord
import GroupApproximation.Computability.AdianRabinWordProblem
import GroupApproximation.Higman.BridgePresentation
import GroupApproximation.Higman.CurrentREBenign
import GroupApproximation.Manuscript.MFRecognition.FixedUniversalFamilyRecursive
import GroupApproximation.Manuscript.MFRecognition.FixedUniversalHostCompiler

/-!
# The fixed universal marked host from Omega

The concrete rank-three family embeds in one recursively presented free
product.  We apply the effective HNN bridge to that group and Higman's
embedding theorem once.  The resulting finite host is constant.  The only
varying output is the three words spelling the bridge words at indices
`3e`, `3e+1`, and `3e+2`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace FixedUniversalHostOfOmega

open Higman
open PresentationCodes
open TwoSidedConcreteQCodeFamily

noncomputable section

abbrev Universal : Type := FixedUniversalFamily.U indexedQcode

def universalPresentation : RecursivePresentation Universal :=
  FixedUniversalFamilyRecursive.recursivePresentationUniversal

/-- The once-only three-generator bridge of the universal family. -/
abbrev UniversalBridge : Type :=
  HNNEmb.Ext universalPresentation.gen

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

/-! ## Raw representatives and the varying bridge words -/

def hostRawEval (hOmega : Omega.OmegaInput) (w : RawWord) :
    Host (hostCode hOmega) :=
  hostQuotient (hostCode hOmega) (wordOf (hostCode hOmega) w)

theorem hostRawEval_surjective (hOmega : Omega.OmegaInput) :
    Function.Surjective (hostRawEval hOmega) :=
  (PresentedGroup.mk_surjective (hostRelators (hostCode hOmega))).comp
    (AdianRabinWordProblem.wordOf_surjective (hostCode hOmega))

def rawOf (hOmega : Omega.OmegaInput) (g : Host (hostCode hOmega)) : RawWord :=
  Function.surjInv (hostRawEval_surjective hOmega) g

@[simp] theorem hostRawEval_rawOf (hOmega : Omega.OmegaInput)
    (g : Host (hostCode hOmega)) : hostRawEval hOmega (rawOf hOmega g) = g :=
  Function.surjInv_eq (hostRawEval_surjective hOmega) g

def rawX (hOmega : Omega.OmegaInput) : RawWord :=
  rawOf hOmega (bridgeHostEmb hOmega
    (BridgeEff.gen3 universalPresentation.gen 0))

def rawY (hOmega : Omega.OmegaInput) : RawWord :=
  rawOf hOmega (bridgeHostEmb hOmega
    (BridgeEff.gen3 universalPresentation.gen 1))

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

/-- The three marked words for input `e`. -/
def wordX (hOmega : Omega.OmegaInput) (e : ℕ) : RawWord :=
  markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega) (3 * e)

def wordY (hOmega : Omega.OmegaInput) (e : ℕ) : RawWord :=
  markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega) (3 * e + 1)

def wordT (hOmega : Omega.OmegaInput) (e : ℕ) : RawWord :=
  markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega) (3 * e + 2)

theorem computable_wordX (hOmega : Omega.OmegaInput) : Computable (wordX hOmega) :=
  (primrec_markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega)).to_comp.comp
    (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id).to_comp

theorem computable_wordY (hOmega : Omega.OmegaInput) : Computable (wordY hOmega) :=
  (primrec_markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega)).to_comp.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
      (Primrec.const 1)).to_comp

theorem computable_wordT (hOmega : Omega.OmegaInput) : Computable (wordT hOmega) :=
  (primrec_markedBridgeRaw (rawX hOmega) (rawY hOmega) (rawT hOmega)).to_comp.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
      (Primrec.const 2)).to_comp

/-! ## The closed fixed-host compiler -/

def compiler (hOmega : Omega.OmegaInput) :
    FixedUniversalHostCompiler indexedQcode where
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
  sourceEmb := FixedUniversalFamily.sourceEmb indexedQcode
  sourceEmb_injective := FixedUniversalFamily.sourceEmb_injective indexedQcode
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
      change FixedUniversalFamilyRecursive.carrierEquivUniversal
          (PresentedGroup.of (3 * e)) =
        FixedUniversalFamily.sourceEmb indexedQcode e
          (PresentedGroup.of (0 : Fin 3))
      rw [FixedUniversalFamilyRecursive.carrierEquivUniversal_of,
        FixedUniversalFamily.sourceEmb_of]
      congr 1
    · change hostRawEval hOmega (wordY hOmega e) = _
      unfold wordY
      rw [hostRawEval_markedBridgeRaw, BridgeEff.pi3_bridgeFree]
      apply congrArg (bridgeHostEmb hOmega)
      apply congrArg (HNNEmb.embA universalPresentation.gen)
      change FixedUniversalFamilyRecursive.carrierEquivUniversal
          (PresentedGroup.of (3 * e + 1)) =
        FixedUniversalFamily.sourceEmb indexedQcode e
          (PresentedGroup.of (1 : Fin 3))
      rw [FixedUniversalFamilyRecursive.carrierEquivUniversal_of,
        FixedUniversalFamily.sourceEmb_of]
      congr 1
    · change hostRawEval hOmega (wordT hOmega e) = _
      unfold wordT
      rw [hostRawEval_markedBridgeRaw, BridgeEff.pi3_bridgeFree]
      apply congrArg (bridgeHostEmb hOmega)
      apply congrArg (HNNEmb.embA universalPresentation.gen)
      change FixedUniversalFamilyRecursive.carrierEquivUniversal
          (PresentedGroup.of (3 * e + 2)) =
        FixedUniversalFamily.sourceEmb indexedQcode e
          (PresentedGroup.of (2 : Fin 3))
      rw [FixedUniversalFamilyRecursive.carrierEquivUniversal_of,
        FixedUniversalFamily.sourceEmb_of]
      congr 1

theorem exists_output_of_omega (hOmega : Omega.OmegaInput) (e : ℕ) :
    ∃ o : MarkedHigmanOutput (indexedQcode e),
      o.raw = (compiler hOmega).compile e :=
  (compiler hOmega).exists_output e

end

end FixedUniversalHostOfOmega
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
