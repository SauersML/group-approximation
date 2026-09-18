import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.WellFormed.Decide

/-!
# The word lists of a certificate are primitive recursive

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`
("`Φ(P,n,c)` is a first-order sentence over the reals"), feeding `thm:mf-arithmetic`:
the sentence `Φ(P,n,c)` is produced from `(P, n, c)` by an algorithm.  Its conjuncts
are indexed by the words labelled `S` by the certificate, `sWords P n c`, and by the
dimension `certDim c`.  This file shows both are primitive recursive functions of
`((P, n), c)` (`enc_primrec_sWords`, `enc_primrec_certDim`).

Reducedness is decided through `wf_isReducedRaw_iff` and `wf_primrec_reduce` of
`WellFormed/Decide.lean`.
-/

namespace GroupApproximation.Full.NN11b

open PresentationCodes AdianRabinWordProblem Manuscript.MFRecognition.Certificates

/-- The signed letters of a code form a primitive recursive list. -/
theorem enc_primrec_signedLetters : Primrec signedLetters := by
  have h : Primrec₂ fun (_ : PresentationCode) (i : ℕ) => [(i, true), (i, false)] :=
    Primrec.list_cons.comp (Primrec.pair Primrec.snd (Primrec.const true))
      (Primrec.list_cons.comp (Primrec.pair Primrec.snd (Primrec.const false))
        (Primrec.const ([] : List (ℕ × Bool))))
  exact (Primrec.list_flatMap (Primrec.list_range.comp RawTransformPrimrec.primrec_genCount)
    h).of_eq fun _ => rfl

/-- `rawWordsOfLength` as a `Nat.rec`. -/
theorem enc_rawWordsOfLength_eq (P : PresentationCode) : ∀ m : ℕ,
    rawWordsOfLength P m = Nat.rec (motive := fun _ => List (List (ℕ × Bool))) [[]]
      (fun _ IH => (signedLetters P).flatMap fun a => IH.map fun w => a :: w) m
  | 0 => rfl
  | m + 1 => congrArg (fun L : List (List (ℕ × Bool)) =>
      (signedLetters P).flatMap fun a => L.map fun w => a :: w) (enc_rawWordsOfLength_eq P m)

/-- The raw words of a given length form a primitive recursive list. -/
theorem enc_primrec_rawWordsOfLength : Primrec₂ rawWordsOfLength := by
  have h3 : Primrec₂ fun (q : (PresentationCode × ℕ × List (List (ℕ × Bool))) × (ℕ × Bool))
      (w : List (ℕ × Bool)) => q.2 :: w :=
    Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have h2 : Primrec₂ fun (z : PresentationCode × ℕ × List (List (ℕ × Bool))) (a : ℕ × Bool) =>
      z.2.2.map fun w => a :: w :=
    Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) h3
  have hg : Primrec₂ fun (P : PresentationCode) (q : ℕ × List (List (ℕ × Bool))) =>
      (signedLetters P).flatMap fun a => q.2.map fun w => a :: w :=
    Primrec.list_flatMap (enc_primrec_signedLetters.comp Primrec.fst) h2
  exact (Primrec.nat_rec (f := fun _ : PresentationCode => ([[]] : List (List (ℕ × Bool))))
    (g := fun (P : PresentationCode) (q : ℕ × List (List (ℕ × Bool))) =>
      (signedLetters P).flatMap fun a => q.2.map fun w => a :: w)
    (Primrec.const _) hg).of_eq fun P m => (enc_rawWordsOfLength_eq P m).symm

/-- The raw words of length at most `n` form a primitive recursive list. -/
theorem enc_primrec_rawWordsUpTo : Primrec₂ rawWordsUpTo := by
  have h : Primrec₂ fun (z : PresentationCode × ℕ) (m : ℕ) => rawWordsOfLength z.1 m :=
    enc_primrec_rawWordsOfLength.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  show Primrec fun z : PresentationCode × ℕ => rawWordsUpTo z.1 z.2
  exact (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
    h).of_eq fun _ => rfl

/-- Reducedness of a raw word is a primitive recursive relation. -/
theorem enc_primrecRel_isReducedRaw :
    PrimrecRel fun (w : List (ℕ × Bool)) (P : PresentationCode) => IsReducedRaw P w := by
  have hn : Primrec fun q : List (ℕ × Bool) × PresentationCode =>
      GroupApproximation.Computability.normLetters q.2 q.1 :=
    GroupApproximation.Computability.primrec_normLetters.comp Primrec.snd Primrec.fst
  have h : PrimrecPred fun q : List (ℕ × Bool) × PresentationCode =>
      FreeGroup.reduce (GroupApproximation.Computability.normLetters q.2 q.1) =
        GroupApproximation.Computability.normLetters q.2 q.1 :=
    Primrec.eq.comp (wf_primrec_reduce.comp hn) hn
  show PrimrecPred fun q : List (ℕ × Bool) × PresentationCode => IsReducedRaw q.2 q.1
  exact h.of_eq fun q => (wf_isReducedRaw_iff q.2 q.1).symm

/-- The short reduced words form a primitive recursive list. -/
theorem enc_primrec_shortReducedWords : Primrec₂ shortReducedWords := by
  have hf := PrimrecRel.listFilter enc_primrecRel_isReducedRaw
  show Primrec fun z : PresentationCode × ℕ => shortReducedWords z.1 z.2
  exact (hf.comp enc_primrec_rawWordsUpTo Primrec.fst).of_eq fun _ =>
    List.filter_congr fun _ _ => decide_eq_decide.2 Iff.rfl

/-- The `T`-labelled words of a certificate form a primitive recursive list. -/
theorem enc_primrec_tWords : Primrec tWords :=
  (Primrec.list_map (Primrec.snd (α := ℕ) (β := List (List (ℕ × Bool) × RawCertificate)))
    (Primrec.fst.comp Primrec.snd).to₂).of_eq fun _ => rfl

/-- Not being labelled `T` is a primitive recursive relation. -/
theorem enc_primrecRel_notMem_tWords :
    PrimrecRel fun (w : List (ℕ × Bool)) (c : PrintedCertificate) => w ∉ tWords c := by
  have h : PrimrecRel fun (w : List (ℕ × Bool)) (c : PrintedCertificate) =>
      ∃ a ∈ tWords c, a = w :=
    (PrimrecRel.exists_mem_list Primrec.eq).comp₂ (enc_primrec_tWords.comp₂ Primrec₂.right)
      Primrec₂.left
  exact h.not.of_eq fun w _ =>
    not_congr ⟨fun ⟨_, ha, he⟩ => he ▸ ha, fun hw => ⟨w, hw, rfl⟩⟩

/-- `prop:mf-upper-bound`: the words labelled `S` by a certificate form a primitive
recursive list of `((P, n), c)`. -/
theorem enc_primrec_sWords :
    Primrec fun z : (PresentationCode × ℕ) × PrintedCertificate => sWords z.1.1 z.1.2 z.2 :=
  ((PrimrecRel.listFilter enc_primrecRel_notMem_tWords).comp
    (enc_primrec_shortReducedWords.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)) Primrec.snd).of_eq fun _ =>
    List.filter_congr fun _ _ => decide_eq_decide.2 Iff.rfl

/-- The dimension of a certificate is a primitive recursive function of `((P, n), c)`. -/
theorem enc_primrec_certDim :
    Primrec fun z : (PresentationCode × ℕ) × PrintedCertificate => certDim z.2 :=
  (Primrec.fst.comp Primrec.snd).of_eq fun _ => rfl

end GroupApproximation.Full.NN11b
