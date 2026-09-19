import GroupApproximation.Computability.MFEnumeratedNormalForm
import GroupApproximation.Computability.MFRecognitionPi02
import GroupApproximation.Computability.EnumeratedFixedMarkedQueryCompleteness

/-!
# MF recognition on recursively enumerated presentations is `Π⁰₂`-complete

`MFRecognitionPi02` decides one open challenge against a *finite*
presentation code by a Boolean matrix checker: exact Gaussian-rational
unitary generators, one power/Frobenius certificate per relator, one per
tested word.  That checker never looks past the letters and the relators the
finite code lists.  So a challenge `(W, N, k)` against a recursively
enumerated code is checked by cutting the finite code whose relators are the
enumerated relators at the addresses `0, …, N` and whose alphabet is one
letter past every letter of `W` and of those relators
(`challengeCode`), and handing it to the finite checker unchanged.

The two bridges `toFinite` and `ofFinite` move a unitary microstate between
the countable alphabet and the cut alphabet; on every word whose letters lie
below the cut, displacement is preserved exactly.  Together with the normal
form `isOperatorMF_iff_forall_openAnswersM`, this places MF recognition on
enumerated codes in `Π⁰₂`.  The matching hardness is
`EnumeratedFixedMarkedQueryCompleteness.operatorMFCode_pi02Hard`, proved on
the same syntax from the repository's literal non-MF presentation, so the two
halves pair into a completeness statement with no hypothesis and no
construction datum.

## What this does not say

Nothing here concerns *finite* presentations.  On finite presentation codes
the upper bound `MFRecognitionPi02.operatorMFCode_pi02` is unconditional, and
the lower bound `MFRecognitionSecondLevel.mfCode_pi02Complete_of_compiler`
takes the effective compiler `e ↦ R̂_e` as its one input.

## Research nodes

* `research/mf-recognition-recursive-presentations-is-second-level-complete.md`
  --- the statement proved here, on the natural effective coding of
  countably generated recursively presented groups.
-/

namespace GroupApproximation
namespace MFEnumeratedPi02

open Nat.Partrec ArithmeticalHierarchy Higman EnumeratedPresentationCodes
open SoficEnumeratedPi02 (relatorAt EnumWordProblem exists_voidN_iff
  decodeChallengeN primrec_decodeChallengeN decodeChallengeN_surjective)
open MFMicrostate (Microstate)
open MFRecognitionPi02 (PassesOpen matrixAnswerCheck exists_matrixAnswerCheck_iff
  primrec_matrixAnswerCheck)
open CodedMicrostateEncoding (MatrixAnswer)

noncomputable section

/-! ## The finite code cut from a prefix of the relator stream -/

/-- The finite presentation code on the letters `0, …, b` whose relators are
the enumerated relators at the addresses `0, …, N`. -/
def truncCode (c : PresentationCode) (b N : ℕ) :
    PresentationCodes.PresentationCode :=
  (b, (List.range (N + 1)).map (rawRelator c))

theorem mem_truncCode_relators_iff {c : PresentationCode} {b N : ℕ}
    {r : List (ℕ × Bool)} :
    r ∈ (truncCode c b N).2 ↔ ∃ j, j ≤ N ∧ rawRelator c j = r := by
  show r ∈ (List.range (N + 1)).map (rawRelator c) ↔ _
  constructor
  · intro hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
    exact ⟨j, Nat.lt_succ_iff.1 (List.mem_range.1 hj), rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_map.2 ⟨j, List.mem_range.2 (Nat.lt_succ_of_le hj), rfl⟩

/-! ## Letter bounds -/

/-- One past the sum of the letters of a word; every letter lies below it. -/
def wordBound (w : List (ℕ × Bool)) : ℕ :=
  w.foldr (fun p s => p.1 + 1 + s) 0

theorem lt_wordBound :
    ∀ {w : List (ℕ × Bool)} {p : ℕ × Bool}, p ∈ w → p.1 < wordBound w
  | [], _, hp => by simp at hp
  | q :: t, p, hp => by
      have hcons : wordBound (q :: t) = q.1 + 1 + wordBound t := rfl
      rw [hcons]
      rcases List.mem_cons.1 hp with rfl | hp'
      · omega
      · have := lt_wordBound hp'
        omega

/-- The sum of the word bounds of a list of words. -/
def listBound (L : List (List (ℕ × Bool))) : ℕ :=
  L.foldr (fun w s => wordBound w + s) 0

theorem wordBound_le_listBound :
    ∀ {L : List (List (ℕ × Bool))} {w : List (ℕ × Bool)}, w ∈ L →
      wordBound w ≤ listBound L
  | [], _, hw => by simp at hw
  | u :: t, w, hw => by
      have hcons : listBound (u :: t) = wordBound u + listBound t := rfl
      rw [hcons]
      rcases List.mem_cons.1 hw with rfl | hw'
      · omega
      · have := wordBound_le_listBound hw'
        omega

/-- The letter bound of a challenge: past every letter of the listed words
and of the relators at the addresses `0, …, N`. -/
def challengeBound (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (N : ℕ) : ℕ :=
  listBound (W ++ (List.range (N + 1)).map (rawRelator c))

theorem lt_challengeBound_of_mem_words (c : PresentationCode)
    {W : List (List (ℕ × Bool))} (N : ℕ) {w : List (ℕ × Bool)} (hw : w ∈ W)
    {p : ℕ × Bool} (hp : p ∈ w) : p.1 < challengeBound c W N :=
  lt_of_lt_of_le (lt_wordBound hp)
    (wordBound_le_listBound (List.mem_append_left _ hw))

theorem lt_challengeBound_of_relator (c : PresentationCode)
    (W : List (List (ℕ × Bool))) {N j : ℕ} (hj : j ≤ N)
    {p : ℕ × Bool} (hp : p ∈ rawRelator c j) : p.1 < challengeBound c W N :=
  lt_of_lt_of_le (lt_wordBound hp)
    (wordBound_le_listBound (List.mem_append_right _
      (List.mem_map.2 ⟨j, List.mem_range.2 (Nat.lt_succ_of_le hj), rfl⟩)))

/-- The finite presentation code a challenge is checked against. -/
def challengeCode (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (N : ℕ) : PresentationCodes.PresentationCode :=
  truncCode c (challengeBound c W N) N

theorem letters_lt_genCount_of_mem_words (c : PresentationCode)
    {W : List (List (ℕ × Bool))} (N : ℕ) {w : List (ℕ × Bool)} (hw : w ∈ W) :
    ∀ p ∈ w, p.1 < PresentationCodes.genCount (challengeCode c W N) :=
  fun _ hp => Nat.lt_succ_of_lt (lt_challengeBound_of_mem_words c N hw hp)

theorem letters_lt_genCount_of_relator (c : PresentationCode)
    (W : List (List (ℕ × Bool))) {N j : ℕ} (hj : j ≤ N) :
    ∀ p ∈ rawRelator c j,
      p.1 < PresentationCodes.genCount (challengeCode c W N) :=
  fun _ hp => Nat.lt_succ_of_lt (lt_challengeBound_of_relator c W hj hp)

/-! ## Moving microstates between the two alphabets -/

/-- Evaluating a raw word through `wordOf` is evaluating it letterwise on the
reduced letters. -/
theorem lift_wordOf {Y : FiniteModel} (c' : PresentationCodes.PresentationCode)
    (g : Fin (PresentationCodes.genCount c') → Matrix.unitaryGroup Y ℂ) :
    ∀ w : List (ℕ × Bool),
      FreeGroup.lift g (PresentationCodes.wordOf c' w)
        = evalRaw (fun i => g (PresentationCodes.letterOf c' i)) w
  | [] => by
      rw [RawWord.wordOf_nil, map_one, evalRaw_nil]
  | (i, true) :: w => by
      rw [RawWord.wordOf_cons_pos, map_mul, FreeGroup.lift_apply_of, lift_wordOf c' g w]
      rfl
  | (i, false) :: w => by
      rw [RawWord.wordOf_cons_neg, map_mul, map_inv, FreeGroup.lift_apply_of,
        lift_wordOf c' g w]
      rfl

/-- Evaluation depends only on the generators at the letters of the word. -/
theorem evalRaw_congr {A : Type} [Group A] {x y : ℕ → A} :
    ∀ w : List (ℕ × Bool), (∀ p ∈ w, x p.1 = y p.1) →
      evalRaw x w = evalRaw y w
  | [], _ => rfl
  | (i, s) :: w, h => by
      have hi : x i = y i := h (i, s) List.mem_cons_self
      rw [evalRaw_cons, evalRaw_cons, hi,
        evalRaw_congr w fun p hp => h p (List.mem_cons_of_mem _ hp)]

/-- A microstate on the countable alphabet, restricted to the letters of a
finite code. -/
def toFinite (M : NatMatrixMicrostate) (c' : PresentationCodes.PresentationCode) :
    Microstate c' where
  model := M.model
  card_pos := M.card_pos
  gen := fun j => M.gen (j : ℕ)

/-- Restriction preserves displacement on words whose letters lie below the
alphabet size. -/
theorem toFinite_len (M : NatMatrixMicrostate)
    (c' : PresentationCodes.PresentationCode) (w : List (ℕ × Bool))
    (hw : ∀ p ∈ w, p.1 < PresentationCodes.genCount c') :
    (toFinite M c').len w = M.len w := by
  rw [MFMicrostate.Microstate.len_def, M.len_def]
  show opLength M.model
      (FreeGroup.lift (fun j : Fin (PresentationCodes.genCount c') => M.gen (j : ℕ))
        (PresentationCodes.wordOf c' w))
    = opLength M.model (evalRaw M.gen w)
  rw [lift_wordOf]
  congr 1
  refine evalRaw_congr w fun p hp => ?_
  show M.gen ((PresentationCodes.letterOf c' p.1 :
    Fin (PresentationCodes.genCount c')) : ℕ) = M.gen p.1
  rw [RawWord.letterOf_val_of_lt c' (hw p hp)]

/-- A microstate of a finite code, read on the countable alphabet by reducing
every letter. -/
def ofFinite {c' : PresentationCodes.PresentationCode} (M' : Microstate c') :
    NatMatrixMicrostate where
  model := M'.model
  card_pos := M'.card_pos
  gen := fun i => M'.gen (PresentationCodes.letterOf c' i)

/-- Reduction preserves displacement on every word. -/
theorem ofFinite_len {c' : PresentationCodes.PresentationCode}
    (M' : Microstate c') (w : List (ℕ × Bool)) :
    (ofFinite M').len w = M'.len w := by
  rw [NatMatrixMicrostate.len_def, MFMicrostate.Microstate.len_def]
  show opLength M'.model
      (evalRaw (fun i => M'.gen (PresentationCodes.letterOf c' i)) w)
    = opLength M'.model (FreeGroup.lift M'.gen (PresentationCodes.wordOf c' w))
  rw [lift_wordOf]

/-- **The microstate disjunct is the finite-code open packet at the
challenge's code.** -/
theorem exists_passesOpenM_iff (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (N k : ℕ) :
    (∃ M : NatMatrixMicrostate, PassesOpenM c W N k M) ↔
      ∃ M' : Microstate (challengeCode c W N),
        PassesOpen (challengeCode c W N) W k M' := by
  constructor
  · rintro ⟨M, hrel, hsep⟩
    refine ⟨toFinite M (challengeCode c W N), ?_, ?_⟩
    · intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_truncCode_relators_iff.1 hr
      rw [toFinite_len M _ _ (letters_lt_genCount_of_relator c W hj)]
      exact hrel j hj
    · intro w hw
      rw [toFinite_len M _ _ (letters_lt_genCount_of_mem_words c N hw)]
      exact hsep w hw
  · rintro ⟨M', hrel, hsep⟩
    refine ⟨ofFinite M', ?_, ?_⟩
    · intro j hj
      have hmem : rawRelator c j ∈ (challengeCode c W N).2 :=
        mem_truncCode_relators_iff.2 ⟨j, hj, rfl⟩
      have h := hrel _ hmem
      show (ofFinite M').len (rawRelator c j) < _
      rw [ofFinite_len]
      exact h
    · intro w hw
      rw [ofFinite_len]
      exact hsep w hw

/-! ## The checker -/

/-- The checker input: a code together with a challenge `(W, N, k)`. -/
abbrev CheckInputM : Type := PresentationCode × (List (List (ℕ × Bool)) × ℕ × ℕ)

/-- The search space for one challenge: a raw word with a word-problem
certificate for the void disjunct, paired with a finite matrix answer for the
microstate disjunct. -/
abbrev AnswerDataM : Type := (List (ℕ × Bool) × WordCertificate) × MatrixAnswer

/-- The matrix of the answer search: the void branch through the enumerated
word-problem checker, the microstate branch through the finite matrix checker
at the challenge's finite code. -/
def answerCheckM (x : CheckInputM) (b : AnswerDataM) : Bool :=
  (decide (b.1.1 ∈ x.2.1) && wordCheck (x.1, b.1.1) b.1.2) ||
    matrixAnswerCheck (challengeCode x.1 x.2.1 x.2.2.1) x.2.1 x.2.2.2 b.2

theorem answerCheckM_iff (x : CheckInputM) :
    (∃ b : AnswerDataM, answerCheckM x b = true)
      ↔ AnswersOpenM x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  constructor
  · rintro ⟨⟨⟨w, p⟩, a⟩, hb⟩
    rw [answerCheckM, Bool.or_eq_true] at hb
    rcases hb with h | h
    · exact Or.inl ((exists_voidN_iff x.1 x.2.1).1 ⟨(w, p), h⟩)
    · refine Or.inr ((exists_passesOpenM_iff x.1 x.2.1 x.2.2.1 x.2.2.2).2 ?_)
      exact (exists_matrixAnswerCheck_iff _ _ _).1 ⟨a, h⟩
  · intro hAns
    rcases hAns with hvoid | hM
    · obtain ⟨⟨w, p⟩, h⟩ := (exists_voidN_iff x.1 x.2.1).2 hvoid
      exact ⟨((w, p), default), by
        rw [answerCheckM, Bool.or_eq_true]; exact Or.inl h⟩
    · obtain ⟨a, h⟩ := (exists_matrixAnswerCheck_iff _ _ _).2
        ((exists_passesOpenM_iff x.1 x.2.1 x.2.2.1 x.2.2.2).1 hM)
      exact ⟨((default, default), a), by
        rw [answerCheckM, Bool.or_eq_true]; exact Or.inr h⟩

/-! ## The checker is primitive recursive -/

theorem primrec_wordBound : Primrec wordBound := by
  have hstep : Primrec₂ fun (_ : List (ℕ × Bool)) (z : (ℕ × Bool) × ℕ) =>
      z.1.1 + 1 + z.2 :=
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const 1))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
    fun _ => rfl

theorem primrec_listBound : Primrec listBound := by
  have hstep : Primrec₂ fun (_ : List (List (ℕ × Bool)))
      (z : List (ℕ × Bool) × ℕ) => wordBound z.1 + z.2 :=
    (Primrec.nat_add.comp (primrec_wordBound.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
    fun _ => rfl

/-- The relator prefix of a challenge, as a list of raw words. -/
theorem primrec_relatorPrefix :
    Primrec fun x : PresentationCode × (List (List (ℕ × Bool)) × ℕ) =>
      (List.range (x.2.2 + 1)).map (rawRelator x.1) :=
  (Primrec.list_map
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))
    (primrec_rawRelator.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
    fun _ => rfl

theorem primrec_challengeBound :
    Primrec fun x : PresentationCode × (List (List (ℕ × Bool)) × ℕ) =>
      challengeBound x.1 x.2.1 x.2.2 :=
  (primrec_listBound.comp
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
      primrec_relatorPrefix)).of_eq fun _ => rfl

theorem primrec_challengeCode :
    Primrec fun x : PresentationCode × (List (List (ℕ × Bool)) × ℕ) =>
      challengeCode x.1 x.2.1 x.2.2 :=
  (Primrec.pair primrec_challengeBound primrec_relatorPrefix).of_eq fun _ => rfl

theorem primrec_answerCheckM : Primrec₂ answerCheckM := by
  have hmem : PrimrecPred fun z : CheckInputM × AnswerDataM =>
      z.2.1.1 ∈ z.1.2.1 := by
    have h : PrimrecRel fun (L : List (List (ℕ × Bool)))
        (u : List (ℕ × Bool)) => ∃ a ∈ L, a = u :=
      PrimrecRel.exists_mem_list Primrec.eq
    refine (h.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).of_eq fun z => ?_
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hz
      exact ⟨z.2.1.1, hz, rfl⟩
  have hsearch : Primrec fun z : CheckInputM × AnswerDataM =>
      wordCheck (z.1.1, z.2.1.1) z.2.1.2 :=
    primrec_wordCheck.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hcode : Primrec fun z : CheckInputM × AnswerDataM =>
      challengeCode z.1.1 z.1.2.1 z.1.2.2.1 :=
    primrec_challengeCode.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  have hmatrix : Primrec fun z : CheckInputM × AnswerDataM =>
      matrixAnswerCheck (challengeCode z.1.1 z.1.2.1 z.1.2.2.1) z.1.2.1
        z.1.2.2.2 z.2.2 :=
    primrec_matrixAnswerCheck.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.pair hcode (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
        (Primrec.snd.comp Primrec.snd))
  exact (Primrec.or.comp (Primrec.and.comp hmem.decide hsearch) hmatrix).of_eq
    fun _ => rfl

/-! ## Answering a challenge is recursively enumerable -/

/-- **Answering one open challenge is recursively enumerable.** -/
theorem rePred_answersOpenM :
    REPred fun x : PresentationCode × (List (List (ℕ × Bool)) × ℕ × ℕ) =>
      AnswersOpenM x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  (WordProblemRE.rePred_exists_eq_true primrec_answerCheckM.to_comp).of_eq
    answerCheckM_iff

/-! ## The arithmetical bounds -/

/-- **Recognising operator-MF from a recursively enumerated presentation code
is `Π⁰₂`.** -/
theorem pi02_isOperatorMF_enum :
    Pi02 fun c : PresentationCode => IsOperatorMF (Carrier c) := by
  refine ⟨fun z : PresentationCode × ℕ =>
    AnswersOpenM z.1 (decodeChallengeN z.2).1 (decodeChallengeN z.2).2.1
      (decodeChallengeN z.2).2.2, ?_, ?_⟩
  · have hmap : Computable fun z : PresentationCode × ℕ =>
        (z.1, decodeChallengeN z.2) :=
      (Primrec.pair Primrec.fst
        (primrec_decodeChallengeN.comp Primrec.snd)).to_comp
    exact rePred_answersOpenM.comp hmap
  · intro c
    refine Iff.trans (isOperatorMF_iff_forall_openAnswersM c) ?_
    constructor
    · intro h n
      exact h (decodeChallengeN n).1 (decodeChallengeN n).2.1
        (decodeChallengeN n).2.2
    · intro h W N k
      have hn : AnswersOpenM c (decodeChallengeN (Encodable.encode (W, N, k))).1
          (decodeChallengeN (Encodable.encode (W, N, k))).2.1
          (decodeChallengeN (Encodable.encode (W, N, k))).2.2 :=
        h (Encodable.encode (W, N, k))
      rw [decodeChallengeN_surjective (W, N, k)] at hn
      exact hn

/-- **Recognising failure of operator-MF from a recursively enumerated
presentation code is `Σ⁰₂`.** -/
theorem sigma02_not_isOperatorMF_enum :
    Sigma02 fun c : PresentationCode => ¬ IsOperatorMF (Carrier c) :=
  (sigma02_compl_iff _).2 pi02_isOperatorMF_enum

/-! ## The exact classification

The upper bound above and the hardness
`EnumeratedFixedMarkedQueryCompleteness.operatorMFCode_pi02Hard` are
statements about the same domain, standard recursively enumerated
presentation codes, so they pair.  Neither carries a hypothesis: the hardness
compiles the exact event switch against the repository's literal non-MF
presentation, and the upper bound is proved above from the definition of
operator-MF alone. -/

/-- **Operator-MF of a recursively enumerated presentation is
`Π⁰₂`-complete.**  No hypothesis, no construction datum. -/
theorem mf_enum_pi02Complete :
    Pi02Complete fun c : EnumeratedPresentationCodes.PresentationCode =>
      IsOperatorMF (EnumeratedPresentationCodes.Carrier c) :=
  ⟨pi02_isOperatorMF_enum, by
    exact EnumeratedFixedMarkedQueryCompleteness.operatorMFCode_pi02Hard⟩

/-- **Failure of operator-MF of a recursively enumerated presentation is
`Σ⁰₂`-complete.** -/
theorem nonmf_enum_sigma02Complete :
    Sigma02Complete fun c : EnumeratedPresentationCodes.PresentationCode =>
      ¬ IsOperatorMF (EnumeratedPresentationCodes.Carrier c) :=
  pi02Complete_compl mf_enum_pi02Complete

/-! ## The closed form -/

/-- **The exact arithmetical classification of operator-MF on enumerated
presentations**, as a closed proposition. -/
def MFEnumeratedExactClassification : Prop :=
  Pi02Complete (fun c : EnumeratedPresentationCodes.PresentationCode =>
      IsOperatorMF (EnumeratedPresentationCodes.Carrier c)) ∧
    Sigma02Complete (fun c : EnumeratedPresentationCodes.PresentationCode =>
      ¬ IsOperatorMF (EnumeratedPresentationCodes.Carrier c))

/-- **The classification holds.** -/
theorem mfEnumeratedExactClassification : MFEnumeratedExactClassification :=
  ⟨mf_enum_pi02Complete, nonmf_enum_sigma02Complete⟩

end

end MFEnumeratedPi02
end GroupApproximation
