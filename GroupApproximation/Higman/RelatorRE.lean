import GroupApproximation.Higman.RelatorSearch
import GroupApproximation.Higman.BlockComputable

/-!
# A presented group with enumerable relators has a recursively enumerable word problem

This is the general tool the lane has been instantiating by hand:
`Higman.BlockComputable` for the coded direct sum, `Higman.TowerComputable` for
the torsion-free radical, and input (4) `BridgeRecursive` would be a third.

> If a group is presented on a computable generating family by a relator set
> whose membership is a primitive-recursive search, then its word problem is
> recursively enumerable.

`Higman.RelatorSearch` reduced triviality to "a list of conjugation data whose
relators lie in `S`, and a deletion certificate".  Here the relator
memberships are merged into the same certificate by the lookup-list device of
`Higman.BlockSearch`, so the whole thing is one existential over `Primcodable`
data with a decidable matrix, and `WordProblemRE.rePred_exists_eq_true`
finishes it.

The relator search is required to be `Primrec₂` rather than merely
`Computable₂`, because the bounded quantifiers `PrimrecRel.forall_mem_list` and
`PrimrecRel.exists_mem_list` --- which is what the lookup list is *for* --- have
no computable analogue in pinned Mathlib.  Every instance in this development
satisfies it.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.WordProblemRE

variable {A : Type} [Group A]

/-! ## 1.  The certificate -/

/-- A witness of triviality: the conjugation data, a lookup list giving each
relator its enumeration index, and a deletion certificate for the resulting
free-group word. -/
abbrev RelCert : Type :=
  List (RawWord × RawWord) × List ((RawWord × RawWord) × ℕ) × List ℕ

variable (relCheck : RawWord → ℕ → Bool)

/-- The certificate checks out. -/
def RelSolves (w : RawWord) (c : RelCert) : Prop :=
  (∀ p ∈ c.1, ∃ q ∈ c.2.1, q.1 = p ∧ relCheck q.1.2 q.2 = true) ∧
    Computability.applySteps (conjWord₂ c.1 ++ invRaw w) c.2.2 = some []

instance relSolves_decidable (w : RawWord) (c : RelCert) :
    Decidable (RelSolves relCheck w c) := by
  unfold RelSolves
  infer_instance

/-- The matrix of the search. -/
def relCert (w : RawWord) (c : RelCert) : Bool := decide (RelSolves relCheck w c)

theorem relCert_eq_true_iff (w : RawWord) (c : RelCert) :
    relCert relCheck w c = true ↔ RelSolves relCheck w c :=
  decide_eq_true_iff

/-! ## 2.  The certificate is complete -/

theorem evalRaw_eq_one_iff_relCert (gen : ℕ → A) (S : Set (FreeGroup ℕ))
    (hpres : ∀ w : RawWord,
      evalRaw gen w = 1 ↔ freeEval w ∈ Subgroup.normalClosure S)
    (hspec : ∀ v : RawWord,
      freeEval v ∈ symmetrize S ↔ ∃ n, relCheck v n = true)
    (w : RawWord) :
    evalRaw gen w = 1 ↔ ∃ c : RelCert, relCert relCheck w c = true := by
  rw [evalRaw_eq_one_iff_search gen S hpres w]
  constructor
  · rintro ⟨l, hl, is, his⟩
    have hl' : ∀ p ∈ l, ∃ n : ℕ, relCheck p.2 n = true :=
      fun p hp => (hspec p.2).1 (hl p hp)
    obtain ⟨ps, hps⟩ :=
      (forall_mem_exists_iff_exists_lookup l fun p n ↦ relCheck p.2 n).1 hl'
    refine ⟨(l, ps, is), (relCert_eq_true_iff relCheck w _).2 ⟨?_, his⟩⟩
    intro p hp
    obtain ⟨q, hq, hqp, hcheck⟩ := hps p hp
    refine ⟨q, hq, hqp, ?_⟩
    rw [hqp]
    exact hcheck
  · rintro ⟨c, hc⟩
    obtain ⟨hlook, hsteps⟩ := (relCert_eq_true_iff relCheck w c).1 hc
    refine ⟨c.1, ?_, c.2.2, hsteps⟩
    intro p hp
    refine (hspec p.2).2 ?_
    obtain ⟨q, hq, hq1, hq2⟩ := hlook p hp
    exact ⟨q.2, by rw [← hq1] at *; exact hq2⟩

/-! ## 3.  The matrix is computable -/

theorem primrec_conjWord₂ : Primrec conjWord₂ := by
  have hinner : Primrec₂ fun (_ : List (RawWord × RawWord))
      (p : RawWord × RawWord) ↦ p.1 ++ p.2 ++ invRaw p.1 :=
    (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
      (primrec_invRaw.comp (Primrec.fst.comp Primrec.snd))).to₂
  exact Primrec.list_flatten.comp (Primrec.list_map Primrec.id hinner)

theorem primrec_relCert (hrel : Primrec₂ relCheck) :
    Primrec₂ (relCert relCheck) := by
  have hmatch : PrimrecRel fun (q : (RawWord × RawWord) × ℕ)
      (y : (RawWord × RawWord) × (RawWord × RelCert)) ↦
        q.1 = y.1 ∧ relCheck q.1.2 q.2 = true := by
    refine PrimrecPred.and ?_ ?_
    · exact Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    · refine Primrec.eq.comp ?_ (Primrec.const true)
      exact hrel.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)
  have hex : PrimrecRel fun (L : List ((RawWord × RawWord) × ℕ))
      (y : (RawWord × RawWord) × (RawWord × RelCert)) ↦
        ∃ q ∈ L, q.1 = y.1 ∧ relCheck q.1.2 q.2 = true :=
    PrimrecRel.exists_mem_list hmatch
  have hitem : PrimrecRel fun (p : RawWord × RawWord)
      (x : RawWord × RelCert) ↦
        ∃ q ∈ x.2.2.1, q.1 = p ∧ relCheck q.1.2 q.2 = true :=
    PrimrecRel.comp hex
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.pair Primrec.fst Primrec.snd)
  have hall : PrimrecRel fun (L : List (RawWord × RawWord))
      (x : RawWord × RelCert) ↦
        ∀ p ∈ L, ∃ q ∈ x.2.2.1, q.1 = p ∧ relCheck q.1.2 q.2 = true :=
    PrimrecRel.forall_mem_list hitem
  have hlook : PrimrecPred fun x : RawWord × RelCert ↦
      ∀ p ∈ x.2.1, ∃ q ∈ x.2.2.1, q.1 = p ∧ relCheck q.1.2 q.2 = true :=
    PrimrecRel.comp hall (Primrec.fst.comp Primrec.snd)
      Primrec.id
  have hsteps : PrimrecPred fun x : RawWord × RelCert ↦
      Computability.applySteps (conjWord₂ x.2.1 ++ invRaw x.1) x.2.2.2
        = some [] := by
    refine Primrec.eq.comp ?_ (Primrec.const (some []))
    refine Computability.primrec_applySteps.comp ?_
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact Primrec.list_append.comp
      (primrec_conjWord₂.comp (Primrec.fst.comp Primrec.snd))
      (primrec_invRaw.comp Primrec.fst)
  haveI : DecidablePred fun x : RawWord × RelCert ↦ RelSolves relCheck x.1 x.2 :=
    fun x ↦ relSolves_decidable relCheck x.1 x.2
  exact (PrimrecPred.and hlook hsteps).decide.of_eq fun _ ↦ by
    unfold relCert
    exact decide_eq_decide.mpr Iff.rfl

/-! ## 4.  The theorem -/

/-- **A presented group with an enumerable relator set has a recursively
enumerable word problem.** -/
theorem rePred_wordProblem_of_relators (gen : ℕ → A) (S : Set (FreeGroup ℕ))
    (hpres : ∀ w : RawWord,
      evalRaw gen w = 1 ↔ freeEval w ∈ Subgroup.normalClosure S)
    (hrel : Primrec₂ relCheck)
    (hspec : ∀ v : RawWord,
      freeEval v ∈ symmetrize S ↔ ∃ n, relCheck v n = true) :
    REPred fun w : RawWord ↦ evalRaw gen w = 1 :=
  (rePred_exists_eq_true (primrec_relCert relCheck hrel).to_comp).of_eq fun w ↦
    (evalRaw_eq_one_iff_relCert relCheck gen S hpres hspec w).symm

/-! ## 5.  Applying it to an explicitly presented group

The tool asks for `hpres`, that triviality of a raw word is membership of its
free value in the normal closure of the relators.  For a group that *is* a
`PresentedGroup` this is definitional, so the whole hypothesis disappears and
the result becomes a statement about presentations alone. -/

theorem evalRaw_presentedGroup_of (S : Set (FreeGroup ℕ)) (w : RawWord) :
    evalRaw (fun k ↦ (PresentedGroup.of k : PresentedGroup S)) w
      = PresentedGroup.mk S (freeEval w) := by
  have hfam : (fun k ↦ (PresentedGroup.of k : PresentedGroup S))
      = fun k ↦ PresentedGroup.mk S (FreeGroup.of k) := rfl
  rw [hfam, ← map_evalRaw]
  rfl

theorem evalRaw_presentedGroup_eq_one_iff (S : Set (FreeGroup ℕ)) (w : RawWord) :
    evalRaw (fun k ↦ (PresentedGroup.of k : PresentedGroup S)) w = 1
      ↔ freeEval w ∈ Subgroup.normalClosure S := by
  rw [evalRaw_presentedGroup_of]
  exact PresentedGroup.mk_eq_one_iff

/-- **A group presented by an enumerable set of relators on countably many
generators is recursively presented.**

This is the general tool in the form the lane wants: no hypothesis about the
group beyond its presentation, and none about the relators beyond their being
a primitive-recursive search. -/
def recursivePresentationPresentedGroup (S : Set (FreeGroup ℕ))
    (hrel : Primrec₂ relCheck)
    (hspec : ∀ v : RawWord,
      freeEval v ∈ symmetrize S ↔ ∃ n, relCheck v n = true) :
    RecursivePresentation (PresentedGroup S) where
  gen := fun k ↦ PresentedGroup.of k
  spans := PresentedGroup.closure_range_of S
  re := rePred_wordProblem_of_relators relCheck _ S
    (evalRaw_presentedGroup_eq_one_iff S) hrel hspec

end Higman
end GroupApproximation
