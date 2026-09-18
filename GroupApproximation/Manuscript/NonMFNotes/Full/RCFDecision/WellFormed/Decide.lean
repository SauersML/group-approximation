import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificateDerivation
import GroupApproximation.Computability.WordProblemRE

/-!
# Well-formedness of a printed certificate is computable

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, proof sentence `a5c1cde4d5f1`:
"Such an expression is checkable, and its existence forces `w = 1` in `G_P`."

The repository carries the check as the `Decidable` instance
`Manuscript.MFRecognition.Certificates.instDecidableWellFormed`.  This module
shows that the resulting Boolean function of `(P, n, c)` is `Computable`
(`computable_wellFormedDecide`), by proving that the well-formedness predicate
is a primitive recursive predicate (`primrecPred_wellFormed`) and reading off
`decide` with the instance above.

Both halves of the check are equalities in a free group, decided by free
reduction:

* `wf_primrec_reduce` — `FreeGroup.reduce` on `List (ℕ × Bool)` is primitive
  recursive: it is the right fold of the one-letter step `wfReduceStep`
  (`wf_reduce_eq_foldr`).
* `wf_isReducedRaw_iff` — reducedness read in the code's alphabet
  `Fin (genCount P)` is reducedness of the normalised raw word, because free
  reduction commutes with renaming letters injectively (`wf_reduce_map_fst`).
* `wf_exprChecks_iff` — a derivation checks exactly when the normalised test
  word `certWord ++ invWord w` of `WordProblemRE` freely reduces to `[]`.

No new `Primcodable` instance is introduced: every type involved is built from
`ℕ`, `Bool`, products and lists.
-/

namespace GroupApproximation.Full.NN11b

open PresentationCodes AdianRabinWordProblem Manuscript.MFRecognition.Certificates

/-! ## Free reduction is primitive recursive -/

/-- One step of `FreeGroup.reduce`: prepend a letter to an already reduced word,
cancelling against its first letter when they are mutually inverse. -/
def wfReduceStep (hd : ℕ × Bool) : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => [hd]
  | hd2 :: tl2 => if hd.1 = hd2.1 ∧ hd.2 = !hd2.2 then tl2 else hd :: hd2 :: tl2

theorem wf_primrec_reduceStep : Primrec₂ wfReduceStep := by
  have hc : PrimrecPred
      fun r : ((ℕ × Bool) × List (ℕ × Bool)) × ((ℕ × Bool) × List (ℕ × Bool)) =>
        r.1.1.1 = r.2.1.1 ∧ r.1.1.2 = !r.2.1.2 :=
    PrimrecPred.and
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.not.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  have hh : Primrec
      fun r : ((ℕ × Bool) × List (ℕ × Bool)) × ((ℕ × Bool) × List (ℕ × Bool)) =>
        if r.1.1.1 = r.2.1.1 ∧ r.1.1.2 = !r.2.1.2 then r.2.2 else r.1.1 :: r.2.1 :: r.2.2 :=
    Primrec.ite hc (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.list_casesOn Primrec.snd
      (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) hh.to₂).of_eq fun a => by
    rcases a with ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

/-- Free reduction is the right fold of `wfReduceStep`. -/
theorem wf_reduce_eq_foldr :
    ∀ L : List (ℕ × Bool), FreeGroup.reduce L = L.foldr wfReduceStep []
  | [] => rfl
  | hd :: tl => by
    have h : FreeGroup.reduce (hd :: tl) = wfReduceStep hd (FreeGroup.reduce tl) := by
      rw [FreeGroup.reduce.cons]
      cases FreeGroup.reduce tl with
      | nil => rfl
      | cons _ _ => rfl
    exact h.trans (congrArg (wfReduceStep hd) (wf_reduce_eq_foldr tl))

/-- `FreeGroup.reduce` on raw words over `ℕ` is primitive recursive. -/
theorem wf_primrec_reduce :
    Primrec (FreeGroup.reduce : List (ℕ × Bool) → List (ℕ × Bool)) := by
  have hstep : Primrec₂ fun (_ : List (ℕ × Bool)) (q : (ℕ × Bool) × List (ℕ × Bool)) =>
      wfReduceStep q.1 q.2 :=
    wf_primrec_reduceStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hfold : Primrec fun L : List (ℕ × Bool) => L.foldr wfReduceStep [] :=
    (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq fun _ => rfl
  exact hfold.of_eq fun L => (wf_reduce_eq_foldr L).symm

/-! ## Renaming letters commutes with free reduction -/

/-- Free reduction commutes with an injective renaming of the letters. -/
theorem wf_reduce_map_fst {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) :
    ∀ L : List (α × Bool),
      FreeGroup.reduce (L.map fun p => (f p.1, p.2)) =
        (FreeGroup.reduce L).map fun p => (f p.1, p.2)
  | [] => rfl
  | hd :: tl => by
    rw [List.map_cons, FreeGroup.reduce.cons, FreeGroup.reduce.cons, wf_reduce_map_fst hf tl]
    cases FreeGroup.reduce tl with
    | nil => rfl
    | cons hd2 tl2 =>
      show (if f hd.1 = f hd2.1 ∧ hd.2 = !hd2.2 then tl2.map fun p : α × Bool => (f p.1, p.2)
          else (f hd.1, hd.2) :: (f hd2.1, hd2.2) :: tl2.map fun p : α × Bool => (f p.1, p.2)) =
        (if hd.1 = hd2.1 ∧ hd.2 = !hd2.2 then tl2 else hd :: hd2 :: tl2).map
          fun p : α × Bool => (f p.1, p.2)
      by_cases h : hd.1 = hd2.1 ∧ hd.2 = !hd2.2
      · have h' : f hd.1 = f hd2.1 ∧ hd.2 = !hd2.2 := ⟨congrArg f h.1, h.2⟩
        exact (if_pos h').trans
          (congrArg (List.map fun p : α × Bool => (f p.1, p.2))
            (if_pos (t := tl2) (e := hd :: hd2 :: tl2) h)).symm
      · have h' : ¬(f hd.1 = f hd2.1 ∧ hd.2 = !hd2.2) := fun h2 => h ⟨hf h2.1, h2.2⟩
        exact (if_neg h').trans
          (congrArg (List.map fun p : α × Bool => (f p.1, p.2))
            (if_neg (t := tl2) (e := hd :: hd2 :: tl2) h)).symm

/-! ## The two checks as equalities of raw words -/

/-- Reducedness in the code's alphabet is reducedness of the normalised raw word. -/
theorem wf_isReducedRaw_iff (P : PresentationCode) (w : List (ℕ × Bool)) :
    IsReducedRaw P w ↔
      FreeGroup.reduce (GroupApproximation.Computability.normLetters P w) =
        GroupApproximation.Computability.normLetters P w := by
  have hv : Function.Injective fun q : Fin (genCount P) × Bool => ((q.1 : ℕ), q.2) :=
    fun a b h => Prod.ext (Fin.val_injective (congrArg Prod.fst h)) (congrArg Prod.snd h)
  have hnorm : (w.map fun p => (PresentationCodes.letterOf P p.1, p.2)).map
      (fun q : Fin (genCount P) × Bool => ((q.1 : ℕ), q.2)) =
        GroupApproximation.Computability.normLetters P w := by
    rw [List.map_map]
    rfl
  show FreeGroup.reduce (w.map fun p => (PresentationCodes.letterOf P p.1, p.2)) =
      w.map (fun p => (PresentationCodes.letterOf P p.1, p.2)) ↔ _
  rw [← hnorm, wf_reduce_map_fst (f := (Fin.val : Fin (genCount P) → ℕ)) Fin.val_injective]
  exact ⟨fun h => congrArg (List.map fun q : Fin (genCount P) × Bool => ((q.1 : ℕ), q.2)) h,
    fun h => List.map_injective_iff.2 hv h⟩

/-- A derivation checks exactly when the normalised test word of `WordProblemRE`
freely reduces to the empty word. -/
theorem wf_exprChecks_iff (P : PresentationCode) (w : List (ℕ × Bool)) (π : RawCertificate) :
    ExprChecks P w π ↔
      FreeGroup.reduce (GroupApproximation.Computability.normLetters P
        (WordProblemRE.testWord P w π)) = [] := by
  show rawValue P π = PresentationCodes.wordOf P w ↔ _
  rw [← WordProblemRE.wordOf_testWord_eq_one_iff,
    GroupApproximation.Computability.wordOf_eq_one_iff]
  exact (FreeGroup.toWord_eq_nil_iff (α := ℕ)).symm

/-! ## Well-formedness is primitive recursive -/

/-- The input of the well-formedness check: a code, a scale and a certificate. -/
abbrev WellFormedInput : Type := (PresentationCode × ℕ) × PrintedCertificate

/-- A `T`-entry of a certificate: a word with its derivation. -/
abbrev WellFormedEntry : Type := List (ℕ × Bool) × RawCertificate

/-- The per-entry test of `WellFormed` is a primitive recursive relation. -/
theorem wf_primrecRel_entry :
    PrimrecRel fun (e : WellFormedEntry) (z : WellFormedInput) =>
      IsShortReduced z.1.1 z.1.2 e.1 ∧ ExprChecks z.1.1 e.1 e.2 := by
  have hP : Primrec fun q : WellFormedEntry × WellFormedInput => q.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hn : Primrec fun q : WellFormedEntry × WellFormedInput => q.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hw : Primrec fun q : WellFormedEntry × WellFormedInput => q.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hπ : Primrec fun q : WellFormedEntry × WellFormedInput => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hlen : PrimrecPred fun q : WellFormedEntry × WellFormedInput =>
      q.1.1.length ≤ q.2.1.2 :=
    Primrec.nat_le.comp (Primrec.list_length.comp hw) hn
  have hlt : PrimrecRel fun (p : ℕ × Bool) (c : PresentationCode) => p.1 < genCount c :=
    Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst)
      (RawTransformPrimrec.primrec_genCount.comp Primrec.snd)
  have hlet : PrimrecPred fun q : WellFormedEntry × WellFormedInput =>
      ∀ p ∈ q.1.1, p.1 < genCount q.2.1.1 :=
    PrimrecRel.comp (PrimrecRel.forall_mem_list hlt) hw hP
  have hnorm : Primrec fun q : WellFormedEntry × WellFormedInput =>
      GroupApproximation.Computability.normLetters q.2.1.1 q.1.1 :=
    GroupApproximation.Computability.primrec_normLetters.comp hP hw
  have hred : PrimrecPred fun q : WellFormedEntry × WellFormedInput =>
      FreeGroup.reduce (GroupApproximation.Computability.normLetters q.2.1.1 q.1.1) =
        GroupApproximation.Computability.normLetters q.2.1.1 q.1.1 :=
    Primrec.eq.comp (wf_primrec_reduce.comp hnorm) hnorm
  have htest : Primrec fun q : WellFormedEntry × WellFormedInput =>
      WordProblemRE.testWord q.2.1.1 q.1.1 q.1.2 :=
    (Primrec.list_append.comp (WordProblemRE.primrec_certWord.comp hP hπ)
      (RawTransformPrimrec.primrec_invWord.comp hw)).of_eq fun _ => rfl
  have htestNorm : Primrec fun q : WellFormedEntry × WellFormedInput =>
      GroupApproximation.Computability.normLetters q.2.1.1
        (WordProblemRE.testWord q.2.1.1 q.1.1 q.1.2) :=
    GroupApproximation.Computability.primrec_normLetters.comp hP htest
  have hexpr : PrimrecPred fun q : WellFormedEntry × WellFormedInput =>
      FreeGroup.reduce (GroupApproximation.Computability.normLetters q.2.1.1
        (WordProblemRE.testWord q.2.1.1 q.1.1 q.1.2)) = [] :=
    Primrec.eq.comp (wf_primrec_reduce.comp htestNorm) (Primrec.const [])
  show PrimrecPred fun q : WellFormedEntry × WellFormedInput =>
    IsShortReduced q.2.1.1 q.2.1.2 q.1.1 ∧ ExprChecks q.2.1.1 q.1.1 q.1.2
  exact ((hlen.and (hlet.and hred)).and hexpr).of_eq fun q =>
    and_congr (and_congr Iff.rfl (and_congr Iff.rfl (wf_isReducedRaw_iff q.2.1.1 q.1.1).symm))
      (wf_exprChecks_iff q.2.1.1 q.1.1 q.1.2).symm

/-- `prop:mf-upper-bound`, proof sentence `a5c1cde4d5f1` ("Such an expression is
checkable"): well-formedness of a certificate at scale `n` is a primitive
recursive predicate of `(P, n, c)`. -/
theorem primrecPred_wellFormed :
    PrimrecPred fun z : WellFormedInput => WellFormed z.1.1 z.1.2 z.2 := by
  have hcd : Primrec fun z : WellFormedInput => certDim z.2 :=
    (Primrec.fst.comp Primrec.snd).of_eq fun _ => rfl
  have hte : Primrec fun z : WellFormedInput => tEntries z.2 :=
    (Primrec.snd.comp Primrec.snd).of_eq fun _ => rfl
  have hdim : PrimrecPred fun z : WellFormedInput => 1 ≤ certDim z.2 :=
    Primrec.nat_le.comp (Primrec.const 1) hcd
  have hall : PrimrecPred fun z : WellFormedInput =>
      ∀ e ∈ tEntries z.2, IsShortReduced z.1.1 z.1.2 e.1 ∧ ExprChecks z.1.1 e.1 e.2 :=
    PrimrecRel.comp (PrimrecRel.forall_mem_list wf_primrecRel_entry) hte Primrec.id
  exact (hdim.and hall).of_eq fun _ => Iff.rfl

/-- `prop:mf-upper-bound`, proof sentence `a5c1cde4d5f1` ("Such an expression is
checkable"): the Boolean well-formedness check `decide (WellFormed P n c)`,
through the repository's instance `instDecidableWellFormed`, is computable. -/
theorem computable_wellFormedDecide :
    Computable fun z : (PresentationCode × ℕ) × PrintedCertificate =>
      decide (Manuscript.MFRecognition.Certificates.WellFormed z.1.1 z.1.2 z.2) :=
  primrecPred_wellFormed.decide.to_comp

end GroupApproximation.Full.NN11b
