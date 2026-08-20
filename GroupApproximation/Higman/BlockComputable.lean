import GroupApproximation.Higman.BlockSearch

/-!
# The search matrix is computable, and (B1) is proved

`Higman.BlockSearch` reduces the last field of a
`Higman.RecursivePresentation Higman.PCDirectSum` to one unbounded search:

    evalRaw pcGen w = 1  ↔  ∃ ps : BlockData, blockCheck w ps = true .

This file proves `Primrec₂ blockCheck`, which is the last thing (B1) needed,
and assembles the recursive presentation.

## Why every step is available

Each ingredient of `blockCheck` is primitive recursive over `Primcodable`
types, and every lemma used is in pinned Mathlib or already in this
repository:

* `blockOf` is `Encodable.decode` at a `Primcodable` type, after `Nat.unpair`,
  with a default --- `Primrec.unpair`, `Primrec.decode`, `Primrec.option_getD`.
  This is the payoff of indexing the absorber by
  `PresentationCodes.PresentationCode` rather than by the Type-level codes;
  see `Higman.CodedAbsorber`.
* `blockList` and the re-indexing are `Primrec.list_map`.
* the block subword is `PrimrecRel.listFilter`, which is *parameterized*
  filtering --- the predicate may depend on the second argument, which is
  exactly what is needed since the block code is not fixed.
* the two quantifiers are `PrimrecRel.forall_mem_list` and
  `PrimrecRel.exists_mem_list`.  This is why `BlockSearch` uses a lookup list
  rather than a zip: pinned Mathlib has bounded quantifiers over lists and no
  `Primrec` fact for `List.zip`.
* the innermost test is `WordProblemRE.primrec_searchCheck`, already proved.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.PresentationCodes
open GroupApproximation.AdianRabinWordProblem
open GroupApproximation.WordProblemRE

/-! ## 1.  The block map and the letter index -/

theorem primrec_blockOf : Primrec blockOf := by
  have h1 : Primrec fun n : ℕ ↦ n.unpair.1 := Primrec.fst.comp Primrec.unpair
  have h2 : Primrec fun n : ℕ ↦
      Encodable.decode (α := PresentationCode) n.unpair.1 :=
    Primrec.decode.comp h1
  exact (Primrec.option_getD.comp h2
    (Primrec.const ((0, []) : PresentationCode))).of_eq fun _ ↦ rfl

theorem primrec_letterIndex : Primrec letterIndex :=
  (Primrec.snd.comp Primrec.unpair).of_eq fun _ ↦ rfl

theorem primrec_blockList : Primrec blockList := by
  refine (Primrec.list_map Primrec.id ?_).of_eq fun _ ↦ rfl
  exact (primrec_blockOf.comp (Primrec.fst.comp Primrec.snd)).to₂

/-! ## 2.  The block subword -/

theorem primrec_blockWord : Primrec₂ blockWord := by
  have hR : PrimrecRel fun (p : ℕ × Bool) (c : PresentationCode) ↦
      blockOf p.1 = c :=
    Primrec.eq.comp (primrec_blockOf.comp (Primrec.fst.comp Primrec.fst))
      Primrec.snd
  have hfil : Primrec fun z : RawWord × PresentationCode ↦
      z.1.filter fun p ↦ decide (blockOf p.1 = z.2) :=
    PrimrecRel.listFilter hR
  have hmap : Primrec₂ fun (_ : RawWord × PresentationCode) (p : ℕ × Bool) ↦
      ((letterIndex p.1, p.2) : ℕ × Bool) :=
    (Primrec.pair (primrec_letterIndex.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_map hfil hmap).of_eq fun _ ↦ rfl

/-! ## 3.  The matrix -/

theorem primrec_blockCheck : Primrec₂ blockCheck := by
  have hS : PrimrecRel fun (q : PresentationCode × SearchData)
      (y : PresentationCode × RawWord) ↦
        q.1 = y.1 ∧ searchCheck (y.1, blockWord y.2 y.1) q.2 = true := by
    refine PrimrecPred.and ?_ ?_
    · exact Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    · refine Primrec.eq.comp ?_ (Primrec.const true)
      refine primrec_searchCheck.comp ?_ (Primrec.snd.comp Primrec.fst)
      exact Primrec.pair (Primrec.fst.comp Primrec.snd)
        (primrec_blockWord.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.fst.comp Primrec.snd))
  have hE : PrimrecRel fun (L : BlockData) (y : PresentationCode × RawWord) ↦
      ∃ q ∈ L, q.1 = y.1 ∧
        searchCheck (y.1, blockWord y.2 y.1) q.2 = true :=
    PrimrecRel.exists_mem_list hS
  have hT : PrimrecRel fun (c : PresentationCode) (x : RawWord × BlockData) ↦
      ∃ q ∈ x.2, q.1 = c ∧
        searchCheck (c, blockWord x.1 c) q.2 = true :=
    PrimrecRel.comp hE (Primrec.snd.comp Primrec.snd)
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have hF : PrimrecRel fun (L : List PresentationCode)
      (x : RawWord × BlockData) ↦
        ∀ c ∈ L, ∃ q ∈ x.2, q.1 = c ∧
          searchCheck (c, blockWord x.1 c) q.2 = true :=
    PrimrecRel.forall_mem_list hT
  have hP : PrimrecPred fun x : RawWord × BlockData ↦ BlockSolves x.1 x.2 :=
    PrimrecRel.comp hF (primrec_blockList.comp Primrec.fst) Primrec.id
  haveI : DecidablePred fun x : RawWord × BlockData ↦ BlockSolves x.1 x.2 :=
    fun x ↦ blockSolves_decidable x.1 x.2
  exact hP.decide.of_eq fun _ ↦ rfl

theorem computable_blockCheck : Computable₂ blockCheck :=
  primrec_blockCheck.to_comp

/-! ## 4.  (B1) -/

/-- **(B1), proved.**  The restricted direct product of the groups of all
Primcodable presentation codes is recursively presented: the generating family
is `pcGen`, it spans by `spans_pcGen`, and its word problem is one unbounded
search whose matrix is `blockCheck`. -/
def recursivePresentationPCDirectSum : RecursivePresentation PCDirectSum where
  gen := pcGen
  spans := spans_pcGen
  re := (rePred_exists_eq_true computable_blockCheck).of_eq fun w ↦
    (evalRaw_pcGen_eq_one_iff_blockCheck w).symm

end Higman
end GroupApproximation
