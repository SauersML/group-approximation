import GroupApproximation.Higman.TowerComputable
import GroupApproximation.Higman.BlockTower

/-!
# (B2), closed

`Higman.BlockTower` reduces the absorber's word problem to a conjunction, over
the blocks of `w`, of `∃ i, TowerDeriv (codedGen c) i (blockWord w c)`; and
`Higman.TowerComputable` makes each conjunct one unbounded search with a
computable matrix.  This file merges the searches, exactly as
`Higman.BlockSearch` merged (B1)'s: a witness is a lookup list pairing each
block with the certificate for that block, and the whole check is again
`∀ c ∈ blockList w, ∃ q ∈ ps, …`, the bounded-quantifier shape that
`PrimrecRel.forall_mem_list` and `PrimrecRel.exists_mem_list` make primitive
recursive.

The result is `recursivePresentationPCAbsorberFull`, an unconditional
`Higman.RecursivePresentation Higman.PCAbsorber`.  Together with
`Higman.recursivePresentationPCDirectSum` that is all of Chiodo's Proposition
3.8 at the absorber, so **input (B) of `Higman.Program` is discharged** and
`ChiodoBelegradek.Statement` rests on Higman's embedding theorem alone.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.PresentationCodes
open GroupApproximation.AdianRabinWordProblem
open GroupApproximation.WordProblemRE

/-! ## 1.  The merged search -/

/-- Every block of `w` has a tower certificate in the lookup list. -/
def TowerSolves (w : RawWord)
    (ps : List (PresentationCode × List Entry)) : Prop :=
  ∀ c ∈ blockList w, ∃ q ∈ ps,
    q.1 = c ∧ certCheck c (blockWord w c) q.2 = true

instance towerSolves_decidable (w : RawWord)
    (ps : List (PresentationCode × List Entry)) :
    Decidable (TowerSolves w ps) := by
  unfold TowerSolves
  infer_instance

/-- The matrix of the merged search. -/
def towerCheck (w : RawWord)
    (ps : List (PresentationCode × List Entry)) : Bool :=
  decide (TowerSolves w ps)

theorem towerCheck_eq_true_iff (w : RawWord)
    (ps : List (PresentationCode × List Entry)) :
    towerCheck w ps = true ↔ TowerSolves w ps :=
  decide_eq_true_iff

theorem evalRaw_quotient_eq_one_iff_towerCheck (w : RawWord) :
    evalRaw (quotientGen pcGen) w = 1 ↔
      ∃ ps : List (PresentationCode × List Entry), towerCheck w ps = true := by
  rw [evalRaw_quotient_eq_one_iff_towerDeriv]
  have h : (∀ c ∈ blockList w, ∃ i : ℕ,
        TowerDeriv (codedGen c) i (blockWord w c)) ↔
      ∀ c ∈ blockList w, ∃ L : List Entry,
        certCheck c (blockWord w c) L = true :=
    forall_congr' fun c => imp_congr_right fun _ =>
      towerDeriv_iff_exists_certCheck c (blockWord w c)
  change (∀ c ∈ blockList w, ∃ i : ℕ,
      TowerDeriv (codedGen c) i (blockWord w c)) ↔ _
  rw [h]
  refine (forall_mem_exists_iff_exists_lookup (blockList w)
    (fun c L ↦ certCheck c (blockWord w c) L)).trans ?_
  constructor
  · rintro ⟨ps, hps⟩
    exact ⟨ps, (towerCheck_eq_true_iff w ps).2 hps⟩
  · rintro ⟨ps, hps⟩
    exact ⟨ps, (towerCheck_eq_true_iff w ps).1 hps⟩

/-! ## 2.  The matrix is computable -/

theorem primrec_towerCheck : Primrec₂ towerCheck := by
  have hinner : PrimrecRel fun (q : PresentationCode × List Entry)
      (y : PresentationCode × RawWord) ↦
        q.1 = y.1 ∧ certCheck y.1 (blockWord y.2 y.1) q.2 = true := by
    refine PrimrecPred.and ?_ ?_
    · exact Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    · refine Primrec.eq.comp ?_ (Primrec.const true)
      exact primrec_certCheck.comp (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (primrec_blockWord.comp (Primrec.snd.comp Primrec.snd)
            (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.fst))
  have hex : PrimrecRel fun (L : List (PresentationCode × List Entry))
      (y : PresentationCode × RawWord) ↦
        ∃ q ∈ L, q.1 = y.1 ∧ certCheck y.1 (blockWord y.2 y.1) q.2 = true :=
    PrimrecRel.exists_mem_list hinner
  have hT : PrimrecRel fun (c : PresentationCode)
      (x : RawWord × List (PresentationCode × List Entry)) ↦
        ∃ q ∈ x.2, q.1 = c ∧ certCheck c (blockWord x.1 c) q.2 = true :=
    PrimrecRel.comp hex (Primrec.snd.comp Primrec.snd)
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have hF : PrimrecRel fun (L : List PresentationCode)
      (x : RawWord × List (PresentationCode × List Entry)) ↦
        ∀ c ∈ L, ∃ q ∈ x.2, q.1 = c ∧
          certCheck c (blockWord x.1 c) q.2 = true :=
    PrimrecRel.forall_mem_list hT
  have hP : PrimrecPred fun x : RawWord × List (PresentationCode × List Entry) ↦
      TowerSolves x.1 x.2 := by
    unfold TowerSolves
    exact PrimrecRel.comp hF (primrec_blockList.comp Primrec.fst) Primrec.id
  haveI : DecidablePred fun x : RawWord × List (PresentationCode × List Entry) ↦
      TowerSolves x.1 x.2 := fun x ↦ towerSolves_decidable x.1 x.2
  exact hP.decide.of_eq fun _ ↦ by
    unfold towerCheck
    exact decide_eq_decide.mpr Iff.rfl

/-! ## 3.  (B2) -/

/-- **(B2), proved.**  The absorber is recursively presented: its generating
family is the image of `pcGen`, it spans, and its word problem is one unbounded
search whose matrix is `towerCheck`.

This is Chiodo's Proposition 3.8 at the absorber, and with
`Higman.recursivePresentationPCDirectSum` it discharges input (B) of
`Higman.Program`. -/
noncomputable def recursivePresentationPCAbsorberFull : RecursivePresentation PCAbsorber where
  gen := quotientGen pcGen
  spans := spans_quotientGen spans_pcGen
  re := (rePred_exists_eq_true primrec_towerCheck.to_comp).of_eq fun w ↦
    (evalRaw_quotient_eq_one_iff_towerCheck w).symm

end Higman
end GroupApproximation
