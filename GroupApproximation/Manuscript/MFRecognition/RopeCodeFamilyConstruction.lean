import GroupApproximation.Manuscript.MFRecognition.RecognitionAssembly
import GroupApproximation.Manuscript.MFRecognition.CentralRopeGenerators
import GroupApproximation.Higman.MikhailovaRankThreeCode
import GroupApproximation.Higman.MikhailovaRopeCodeSemantics
import GroupApproximation.Computability.BenignInfCodeSemantics

/-!
# `lem:finite-rope`, second sentence: the code of `R̂_e`

> *"A code of the finite presentation `eq:finite-rope` is computable from
> `e`.  Computability of the code follows from `lem:mikhailova` and
> `lem:central-rope`."*

This module builds the `RopeCodeFamily` datum of `RecognitionAssembly` from a
marked Higman output family whose raw data is computable: the code of `R̂_e`
is `Higman.MikhailovaRopeCode.compile` applied to

* the ambient code of `K_e = (F × F(X_e) × F(X_e)) × (F × P)`, a product of
  free-group codes;
* the cutting words generating `L_e`, which are the rank-three cutting words
  of `Higman.MikhailovaRankThreeCode` (the basis of `F`, the diagonal pairs,
  the relator pairs) placed in the left factor, and the three graph words
  `(a, jq₊(a))` placed in the right factor;
* the marked words `i(x), i(y), i(t)`.

Its semantics is `Higman.MikhailovaRopeCodeSemantics.compileEquivToRope` at
the benign witness `RopeObjects.witness`, whose three hypotheses are proved
here from `CentralRopeGenerators.Le_eq_closure_gens` and the generator
computations of the product codes.
-/

namespace GroupApproximation

open PresentationCodes DirectProductCode DirectProductCodeSemantics
open BenignInfCodeSemantics Higman

/-! ## Free-group codes -/

namespace FreeCodeSemantics

theorem normalClosure_empty {G : Type*} [Group G] :
    Subgroup.normalClosure (∅ : Set G) = ⊥ :=
  le_antisymm (Subgroup.normalClosure_le_normal (Set.empty_subset _)) bot_le

@[simp] theorem relatorFinset_presentationSkeleton (n : ℕ) :
    relatorFinset (MikhailovaRopeCode.presentationSkeleton n) = ∅ := rfl

theorem codeRels_presentationSkeleton (n : ℕ) :
    codeRels (MikhailovaRopeCode.presentationSkeleton n) = ∅ :=
  Finset.coe_eq_empty.mpr (relatorFinset_presentationSkeleton n)

/-- The code with no relators presents the free group on its alphabet. -/
noncomputable def freeCodeEquiv (n : ℕ) :
    Carrier (MikhailovaRopeCode.presentationSkeleton n) ≃* FreeGroup (Fin (n + 1)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (by
        show Subgroup.normalClosure
            (codeRels (MikhailovaRopeCode.presentationSkeleton n)) = ⊥
        rw [codeRels_presentationSkeleton, normalClosure_empty])).trans
    QuotientGroup.quotientBot

/-- The free-code equivalence reads a raw word as the free-group word it
spells. -/
@[simp] theorem freeCodeEquiv_evalWord (n : ℕ) (w : List (ℕ × Bool)) :
    freeCodeEquiv n (evalWord (MikhailovaRopeCode.presentationSkeleton n) w)
      = wordOf (MikhailovaRopeCode.presentationSkeleton n) w := rfl

theorem letterOf_presentationSkeleton {n i : ℕ} (h : i < n + 1) :
    letterOf (MikhailovaRopeCode.presentationSkeleton n) i = ⟨i, h⟩ :=
  Fin.ext (Nat.mod_eq_of_lt h)

theorem freeCodeEquiv_gen {n i : ℕ} (h : i < n + 1) :
    freeCodeEquiv n (evalWord (MikhailovaRopeCode.presentationSkeleton n) [(i, true)])
      = FreeGroup.of ⟨i, h⟩ := by
  rw [freeCodeEquiv_evalWord, RawWord.wordOf_pos, letterOf_presentationSkeleton h]
  exact rfl

end FreeCodeSemantics

/-! ## The ambient code of `K_e` -/

namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace RopeCodes

open FreeCodeSemantics
open MikhailovaRopeCode hiding Raw
open Rope Rope.RopeInput
open Assembly

/-- The raw marked output: the host code and the three marked words. -/
abbrev RawData : Type := RawMarkedOutput

noncomputable section

/-- The free-group code on three letters. -/
def F3 : PresentationCode := presentationSkeleton 2

/-- The free-group code on two letters. -/
def F2 : PresentationCode := presentationSkeleton 1

/-- The free-group code on the host alphabet. -/
def hostFree (r : RawData) : PresentationCode := presentationSkeleton r.1.1

/-- The code of `K⁰_e = F × F(X_e) × F(X_e)`. -/
def k0Code (r : RawData) : PresentationCode :=
  productCode F3 (productCode (hostFree r) (hostFree r))

/-- The code of `K^g = F × P`, `P = F(x₁,y) × F(x₂,t)`. -/
def kgCode : PresentationCode := productCode F3 (productCode F2 F2)

/-- The code of `K_e = K⁰_e × K^g`. -/
def keCode (r : RawData) : PresentationCode := productCode (k0Code r) kgCode

/-! ### Raw words -/

/-- A `K⁰_e` word, read in `K_e`. -/
def k0Left (r : RawData) (w : Raw) : Raw := leftWord (k0Code r) w

/-- A `K^g` word, read in `K_e`. -/
def kgRight (r : RawData) (w : Raw) : Raw := rightWord (k0Code r) kgCode w

/-- The `i`-th generator of the factor `F` of `K^g`. -/
def kgSrc (i : ℕ) : Raw := leftWord F3 [(i, true)]

/-- A `P` word, read in `K^g`. -/
def kgP (w : Raw) : Raw := rightWord F3 (productCode F2 F2) w

/-- A word of the first factor of `P`. -/
def pL (w : Raw) : Raw := leftWord F2 w

/-- A word of the second factor of `P`. -/
def pR (w : Raw) : Raw := rightWord F2 F2 w

/-- The word spelling `jq₊(x) = (x₁, x₂)`. -/
def jqX : Raw := pL [(0, true)] ++ pR [(0, true)]

/-- The word spelling `jq₊(y) = (y, 1)`. -/
def jqY : Raw := pL [(1, true)]

/-- The word spelling `jq₊(t) = (1, t)`. -/
def jqT : Raw := pR [(1, true)]

/-- The three graph words `(a, jq₊(a))`, read in `K_e`. -/
def graphWords (r : RawData) : List Raw :=
  [kgRight r (kgSrc 0 ++ kgP jqX), kgRight r (kgSrc 1 ++ kgP jqY),
    kgRight r (kgSrc 2 ++ kgP jqT)]

/-- The rank-three cutting words of `L⁰_e`, read in `K_e`. -/
def k0Cutting (r : RawData) : List Raw :=
  (MikhailovaRankThreeCode.cuttingWords r).map (k0Left r)

/-- The cutting words generating `L_e`. -/
def cuttingWordsKe (r : RawData) : List Raw := k0Cutting r ++ graphWords r

/-- The marked word `i(a)`, from the rank-three marked word of `a`. -/
def markedKe (r : RawData) (i : ℕ) (w : Raw) : Raw :=
  k0Left r w ++ kgRight r (kgSrc i)

/-- The three marked pairs `(a, i(a))`. -/
def markedList (r : RawData) : List (Raw × Raw) :=
  [([(0, true)], markedKe r 0 (MikhailovaRankThreeCode.markedZero r)),
    ([(1, true)], markedKe r 1 (MikhailovaRankThreeCode.markedOne r)),
    ([(2, true)], markedKe r 2 (MikhailovaRankThreeCode.markedTwo r))]

/-- The rope input, and the code of `R̂_e`. -/
def ropeCode (r : RawData) : PresentationCode :=
  MikhailovaRopeCode.compile (keCode r, (F3, (cuttingWordsKe r, markedList r)))

/-! ### Computability -/

theorem primrec_hostFree : Primrec hostFree :=
  primrec_presentationSkeleton.comp (Primrec.fst.comp Primrec.fst)

theorem primrec_k0Code : Primrec k0Code :=
  primrec_productCode.comp (Primrec.pair (Primrec.const F3)
    (primrec_productCode.comp (Primrec.pair primrec_hostFree primrec_hostFree)))

theorem primrec_keCode : Primrec keCode :=
  primrec_productCode.comp (Primrec.pair primrec_k0Code (Primrec.const kgCode))

theorem primrec_k0Left : Primrec₂ k0Left := by
  have h : Primrec (fun z : RawData × Raw => leftWord (k0Code z.1) z.2) :=
    primrec_leftWord.comp (primrec_k0Code.comp Primrec.fst) Primrec.snd
  exact h

theorem primrec_kgRight : Primrec₂ kgRight := by
  have h : Primrec (fun z : RawData × Raw => rightWord (k0Code z.1) kgCode z.2) :=
    primrec_rightWord.comp (Primrec.pair
      (Primrec.pair (primrec_k0Code.comp Primrec.fst) (Primrec.const kgCode))
      Primrec.snd)
  exact h

theorem primrec_graphWords : Primrec graphWords := by
  have h0 : Primrec (fun r : RawData => kgRight r (kgSrc 0 ++ kgP jqX)) :=
    primrec_kgRight.comp Primrec.id (Primrec.const (kgSrc 0 ++ kgP jqX))
  have h1 : Primrec (fun r : RawData => kgRight r (kgSrc 1 ++ kgP jqY)) :=
    primrec_kgRight.comp Primrec.id (Primrec.const (kgSrc 1 ++ kgP jqY))
  have h2 : Primrec (fun r : RawData => kgRight r (kgSrc 2 ++ kgP jqT)) :=
    primrec_kgRight.comp Primrec.id (Primrec.const (kgSrc 2 ++ kgP jqT))
  exact Primrec.list_cons.comp h0
    (Primrec.list_cons.comp h1
      (Primrec.list_cons.comp h2 (Primrec.const ([] : List Raw))))

theorem primrec_k0Cutting : Primrec k0Cutting := by
  have h : Primrec (fun r : RawData =>
      (MikhailovaRankThreeCode.cuttingWords r).map (k0Left r)) :=
    Primrec.list_map MikhailovaRankThreeCode.primrec_cuttingWords primrec_k0Left
  exact h

theorem primrec_cuttingWordsKe : Primrec cuttingWordsKe := by
  have h : Primrec (fun r : RawData => k0Cutting r ++ graphWords r) :=
    Primrec.list_append.comp primrec_k0Cutting primrec_graphWords
  exact h

theorem primrec_markedZeroRaw :
    Primrec (fun r : RawData => MikhailovaRankThreeCode.markedZero r) :=
  Primrec.fst.comp MikhailovaRankThreeCode.primrec_markedWords

theorem primrec_markedOneRaw :
    Primrec (fun r : RawData => MikhailovaRankThreeCode.markedOne r) :=
  Primrec.fst.comp (Primrec.snd.comp MikhailovaRankThreeCode.primrec_markedWords)

theorem primrec_markedTwoRaw :
    Primrec (fun r : RawData => MikhailovaRankThreeCode.markedTwo r) :=
  Primrec.snd.comp (Primrec.snd.comp MikhailovaRankThreeCode.primrec_markedWords)

theorem primrec_markedZeroKe :
    Primrec (fun r : RawData =>
      markedKe r 0 (MikhailovaRankThreeCode.markedZero r)) := by
  have hleft : Primrec (fun r : RawData =>
      k0Left r (MikhailovaRankThreeCode.markedZero r)) :=
    primrec_k0Left.comp Primrec.id primrec_markedZeroRaw
  have hright : Primrec (fun r : RawData => kgRight r (kgSrc 0)) :=
    primrec_kgRight.comp Primrec.id (Primrec.const (kgSrc 0))
  exact Primrec.list_append.comp hleft hright

theorem primrec_markedOneKe :
    Primrec (fun r : RawData =>
      markedKe r 1 (MikhailovaRankThreeCode.markedOne r)) := by
  have hleft : Primrec (fun r : RawData =>
      k0Left r (MikhailovaRankThreeCode.markedOne r)) :=
    primrec_k0Left.comp Primrec.id primrec_markedOneRaw
  have hright : Primrec (fun r : RawData => kgRight r (kgSrc 1)) :=
    primrec_kgRight.comp Primrec.id (Primrec.const (kgSrc 1))
  exact Primrec.list_append.comp hleft hright

theorem primrec_markedTwoKe :
    Primrec (fun r : RawData =>
      markedKe r 2 (MikhailovaRankThreeCode.markedTwo r)) := by
  have hleft : Primrec (fun r : RawData =>
      k0Left r (MikhailovaRankThreeCode.markedTwo r)) :=
    primrec_k0Left.comp Primrec.id primrec_markedTwoRaw
  have hright : Primrec (fun r : RawData => kgRight r (kgSrc 2)) :=
    primrec_kgRight.comp Primrec.id (Primrec.const (kgSrc 2))
  exact Primrec.list_append.comp hleft hright

theorem primrec_markedList : Primrec markedList := by
  have p0 : Primrec (fun r : RawData =>
      (([(0, true)] : Raw), markedKe r 0 (MikhailovaRankThreeCode.markedZero r))) :=
    Primrec.pair (Primrec.const ([(0, true)] : Raw)) primrec_markedZeroKe
  have p1 : Primrec (fun r : RawData =>
      (([(1, true)] : Raw), markedKe r 1 (MikhailovaRankThreeCode.markedOne r))) :=
    Primrec.pair (Primrec.const ([(1, true)] : Raw)) primrec_markedOneKe
  have p2 : Primrec (fun r : RawData =>
      (([(2, true)] : Raw), markedKe r 2 (MikhailovaRankThreeCode.markedTwo r))) :=
    Primrec.pair (Primrec.const ([(2, true)] : Raw)) primrec_markedTwoKe
  have l2 : Primrec (fun r : RawData =>
      [(([(2, true)] : Raw), markedKe r 2 (MikhailovaRankThreeCode.markedTwo r))]) :=
    Primrec.list_cons.comp p2 (Primrec.const ([] : List (Raw × Raw)))
  have l1 : Primrec (fun r : RawData =>
      [(([(1, true)] : Raw), markedKe r 1 (MikhailovaRankThreeCode.markedOne r)),
        (([(2, true)] : Raw), markedKe r 2 (MikhailovaRankThreeCode.markedTwo r))]) :=
    Primrec.list_cons.comp p1 l2
  exact Primrec.list_cons.comp p0 l1

theorem primrec_ropeCode : Primrec ropeCode := by
  have h : Primrec (fun r : RawData =>
      MikhailovaRopeCode.compile
        (keCode r, (F3, (cuttingWordsKe r, markedList r)))) :=
    MikhailovaRopeCode.primrec_compile.comp
      (Primrec.pair primrec_keCode
        (Primrec.pair (Primrec.const F3)
          (Primrec.pair primrec_cuttingWordsKe primrec_markedList)))
  exact h

theorem computable_ropeCode : Computable ropeCode := primrec_ropeCode.to_comp

end

end RopeCodes
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
