import Mathlib.GroupTheory.FreeGroup.Reduce
import GroupApproximation.Manuscript.MFRecognition.LocalityAndCertificates

/-!
# The printed certificate of `prop:mf-upper-bound`: the object and its
derivations

The first of three modules carrying the printed proof of Proposition
`prop:mf-upper-bound` through the **printed certificate**, one Lean declaration
per printed sentence.  A *certificate at scale `n`* is a triple
`c = (d, ℓ, π)`:

* `d = certDim c`, a dimension `≥ 1`;
* `ℓ`, a labelling of every reduced word of length at most `n` in
  `x_1^{±1}, …, x_k^{±1}` by `T` or `S`, carried as the finite list `tWords c`
  of the words labelled `T` (every other short reduced word is labelled `S`,
  and those are `sWords P n c`);
* `π`, for every `T`-word, a **normal-closure derivation**: a finite list of
  (conjugator, relator, sign) triples whose decoded product is the word.  That
  is the repository's `AdianRabinWordProblem.RawCertificate`, whose decoding is
  `rawValue`; `wordProblem_of_exprChecks` is its soundness.

This module ends with the matrix condition `Φ(P,n,c)` (`PhiSpec`).  The
hypothesis structure carrying Tarski's theorem, the decidability of `C`, and
the forward direction are in `PrintedTarskiCertificateDecision`; the converse
direction and the arithmetical conclusion are in `PrintedTarskiCertificate`.

Printed sentences covered here: `d9548590d33a`, `b8a4a893cbab`,
`a5c1cde4d5f1`, `4b85128c696d`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Certificates

open Matrix PresentationCodes AdianRabinWordProblem RawWord MFMicrostate

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-! ## Small arithmetic and list facts -/

theorem half_pow_le_one (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ m ih =>
      have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
      rw [pow_succ]
      nlinarith

theorem succ_le_two_pow : ∀ n : ℕ, n + 1 ≤ 2 ^ n
  | 0 => by norm_num
  | m + 1 => by
      have ih := succ_le_two_pow m
      have h1 : 0 < 2 ^ m := by positivity
      rw [pow_succ]
      omega

/-- Every positive tolerance eventually absorbs a fixed area count. -/
theorem exists_half_pow_mul_le (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, (N : ℝ) * (1 / 2 : ℝ) ^ n ≤ δ := by
  obtain ⟨n, hn⟩ := Archimedean.arch (N : ℝ) hδ
  rw [nsmul_eq_mul] at hn
  refine ⟨n, ?_⟩
  have hcast : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast succ_le_two_pow n
  have hn2 : (n : ℝ) ≤ (2 : ℝ) ^ n := by linarith
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ n * δ := by nlinarith [hδ.le, hn2, hn]
  have hpow0 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hinv : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc (N : ℝ) * (1 / 2 : ℝ) ^ n
      ≤ ((2 : ℝ) ^ n * δ) * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hNle hpow0.le
    _ = δ * ((1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n) := by ring
    _ = δ := by rw [hinv, mul_one]

theorem half_pow_succ_le (m : ℕ) :
    (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ m := by
  have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
  rw [pow_succ]
  nlinarith

theorem half_pow_antitone : ∀ {a b : ℕ}, a ≤ b →
    (1 / 2 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ a := by
  intro a b
  induction b with
  | zero =>
      intro h
      have ha : a = 0 := Nat.le_zero.1 h
      rw [ha]
  | succ m ih =>
      intro h
      rcases Nat.lt_or_ge a (m + 1) with hlt | hge
      · exact le_trans (half_pow_succ_le m) (ih (Nat.lt_succ_iff.1 hlt))
      · have ha : a = m + 1 := le_antisymm h hge
        rw [ha]

theorem drop_length_le {α : Type*} (i : ℕ) (l : List α) :
    (l.drop i).length ≤ l.length := by
  simp

/-- Reading back the first coordinate of a list of tagged pairs. -/
theorem map_fst_map_pair {α β : Type*} (f : α → β) :
    ∀ l : List α, (l.map fun a => (a, f a)).map Prod.fst = l
  | [] => rfl
  | a :: t => by
      rw [List.map_cons, List.map_cons, map_fst_map_pair f t]

theorem drop_subset' {α : Type*} : ∀ (i : ℕ) (l : List α), l.drop i ⊆ l
  | 0, l => by simp
  | i + 1, [] => by simp
  | i + 1, a :: t => by
      intro x hx
      rw [List.drop_succ_cons] at hx
      exact List.mem_cons_of_mem _ (drop_subset' i t hx)

theorem le_foldr_max : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.foldr max 0
  | [], a, ha => by simp at ha
  | b :: t, a, ha => by
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max t a ha') (le_max_right _ _)

/-! ## The presentation -/

/-- `prop:mf-upper-bound`, proof sentence `d9548590d33a`: "Let
`P = ⟨x_1, …, x_k | r_1, …, r_m⟩`."

A code fixes `k = genCount P` generators and the finite relator list `P.2`; the
relator set is the set of values of the listed relator words, and `G_P` is the
quotient of the free group on the `k` generators by their normal closure, so
that a word dies in `G_P` exactly when it lies in that normal closure. -/
theorem presentation_data (P : PresentationCode) :
    relatorSet P = {r | ∃ u ∈ P.2, wordOf P u = r} ∧
      ∀ w : List (ℕ × Bool),
        WordProblem P w ↔
          wordOf P w ∈ Subgroup.normalClosure (relatorSet P) := by
  constructor
  · ext r
    simp only [Set.mem_setOf_eq]
    exact mem_relatorSet_iff
  · intro w
    exact ⟨wordOf_mem_normalClosure, fun h => PresentedGroup.mk_eq_one_iff.2 h⟩

/-- Every listed relator dies in the coded group. -/
theorem wordProblem_of_mem_relators (P : PresentationCode)
    {r : List (ℕ × Bool)} (hr : r ∈ P.2) : WordProblem P r :=
  PresentedGroup.mk_eq_one_iff.2
    (Subgroup.subset_normalClosure (wordOf_mem_relatorSet hr))

/-! ## Short reduced words -/

/-- Reducedness of a raw word, read in the code's alphabet: the word is its own
free reduction. -/
def IsReducedRaw (P : PresentationCode) (w : List (ℕ × Bool)) : Prop :=
  FreeGroup.reduce (w.map fun p => (letterOf P p.1, p.2))
    = w.map fun p => (letterOf P p.1, p.2)

instance instDecidableIsReducedRaw (P : PresentationCode)
    (w : List (ℕ × Bool)) : Decidable (IsReducedRaw P w) := by
  unfold IsReducedRaw
  infer_instance

/-- The signed alphabet `x_1^{±1}, …, x_k^{±1}` of a code. -/
def signedLetters (P : PresentationCode) : List (ℕ × Bool) :=
  (List.range (genCount P)).flatMap fun i => [(i, true), (i, false)]

theorem mem_signedLetters (P : PresentationCode) (a : ℕ × Bool) :
    a ∈ signedLetters P ↔ a.1 < genCount P := by
  simp only [signedLetters, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨i, hi, (rfl | rfl)⟩ <;> exact hi
  · intro ha
    refine ⟨a.1, ha, ?_⟩
    obtain ⟨i, b⟩ := a
    cases b <;> simp

/-- All raw words of a given length over the signed alphabet. -/
def rawWordsOfLength (P : PresentationCode) : ℕ → List (List (ℕ × Bool))
  | 0 => [[]]
  | m + 1 => (signedLetters P).flatMap fun a =>
      (rawWordsOfLength P m).map fun w => a :: w

/-- All raw words of length at most `n` over the signed alphabet. -/
def rawWordsUpTo (P : PresentationCode) (n : ℕ) : List (List (ℕ × Bool)) :=
  (List.range (n + 1)).flatMap (rawWordsOfLength P)

/-- The domain of the printed labelling `ℓ`: reduced words of length at most
`n` in `x_1^{±1}, …, x_k^{±1}`. -/
def IsShortReduced (P : PresentationCode) (n : ℕ) (w : List (ℕ × Bool)) : Prop :=
  w.length ≤ n ∧ (∀ p ∈ w, p.1 < genCount P) ∧ IsReducedRaw P w

instance instDecidableIsShortReduced (P : PresentationCode) (n : ℕ)
    (w : List (ℕ × Bool)) : Decidable (IsShortReduced P n w) := by
  unfold IsShortReduced
  infer_instance

/-- The reduced words of length at most `n`, enumerated. -/
def shortReducedWords (P : PresentationCode) (n : ℕ) :
    List (List (ℕ × Bool)) :=
  (rawWordsUpTo P n).filter fun w => decide (IsReducedRaw P w)

theorem mem_rawWordsOfLength_iff (P : PresentationCode) :
    ∀ (m : ℕ) (w : List (ℕ × Bool)),
      w ∈ rawWordsOfLength P m ↔
        w.length = m ∧ ∀ p ∈ w, p.1 < genCount P
  | 0, w => by
      constructor
      · intro hw
        have hnil : w = [] := by simpa [rawWordsOfLength] using hw
        subst hnil
        exact ⟨rfl, by simp⟩
      · rintro ⟨hlen, -⟩
        have hnil : w = [] := List.eq_nil_of_length_eq_zero hlen
        subst hnil
        simp [rawWordsOfLength]
  | m + 1, w => by
      constructor
      · intro hw
        simp only [rawWordsOfLength, List.mem_flatMap, List.mem_map] at hw
        obtain ⟨a, ha, u, hu, rfl⟩ := hw
        obtain ⟨hlen, hlet⟩ := (mem_rawWordsOfLength_iff P m u).1 hu
        refine ⟨by simp [hlen], ?_⟩
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp'
        · exact (mem_signedLetters P p).1 ha
        · exact hlet p hp'
      · rintro ⟨hlen, hlet⟩
        cases w with
        | nil => simp at hlen
        | cons a u =>
            simp only [rawWordsOfLength, List.mem_flatMap, List.mem_map]
            refine ⟨a, (mem_signedLetters P a).2 (hlet a List.mem_cons_self),
              u, ?_, rfl⟩
            refine (mem_rawWordsOfLength_iff P m u).2 ⟨by simpa using hlen, ?_⟩
            intro p hp
            exact hlet p (List.mem_cons_of_mem _ hp)

theorem mem_rawWordsUpTo_iff (P : PresentationCode) (n : ℕ)
    (w : List (ℕ × Bool)) :
    w ∈ rawWordsUpTo P n ↔ w.length ≤ n ∧ ∀ p ∈ w, p.1 < genCount P := by
  simp only [rawWordsUpTo, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨m, hm, hw⟩
    obtain ⟨hlen, hlet⟩ := (mem_rawWordsOfLength_iff P m w).1 hw
    exact ⟨by omega, hlet⟩
  · rintro ⟨hlen, hlet⟩
    exact ⟨w.length, by omega,
      (mem_rawWordsOfLength_iff P w.length w).2 ⟨rfl, hlet⟩⟩

/-- The enumeration is exactly the printed domain of the labelling. -/
theorem mem_shortReducedWords_iff (P : PresentationCode) (n : ℕ)
    (w : List (ℕ × Bool)) :
    w ∈ shortReducedWords P n ↔ IsShortReduced P n w := by
  simp only [shortReducedWords, List.mem_filter, decide_eq_true_eq,
    mem_rawWordsUpTo_iff, IsShortReduced]
  tauto

/-! ## The printed certificate -/

/-- `prop:mf-upper-bound`, proof sentence `b8a4a893cbab`: "A *certificate at
scale `n`* is a triple `c = (d, ℓ, π)` consisting of a dimension `d ≥ 1`, a
labelling `ℓ` of every reduced word of length at most `n` in
`x_1^{±1}, …, x_k^{±1}` by one of the symbols `T` and `S`, and, for every word
`w` labelled `T`, an expression of `w` as a product of conjugates of the
relators and their inverses that freely reduces to `w`."

The labelling and the derivations are carried by one finite list: the words
labelled `T`, each paired with its derivation.  Every other short reduced word
is labelled `S`.  The type is a product of `Primcodable` types, so a
certificate is a natural number and `C(P,n,c)` is a relation on triples of
natural numbers, as printed. -/
abbrev PrintedCertificate : Type :=
  ℕ × List (List (ℕ × Bool) × RawCertificate)

/-- The dimension `d` of a certificate. -/
def certDim (c : PrintedCertificate) : ℕ := c.1

/-- The `T`-labelled words of a certificate, each with its derivation `π`. -/
def tEntries (c : PrintedCertificate) :
    List (List (ℕ × Bool) × RawCertificate) := c.2

/-- The words a certificate labels `T`. -/
def tWords (c : PrintedCertificate) : List (List (ℕ × Bool)) :=
  (tEntries c).map Prod.fst

/-- The words a certificate labels `S`: the short reduced words it does not
label `T`. -/
def sWords (P : PresentationCode) (n : ℕ) (c : PrintedCertificate) :
    List (List (ℕ × Bool)) :=
  (shortReducedWords P n).filter fun w => decide (w ∉ tWords c)

theorem mem_sWords_iff (P : PresentationCode) (n : ℕ) (c : PrintedCertificate)
    (w : List (ℕ × Bool)) :
    w ∈ sWords P n c ↔ IsShortReduced P n w ∧ w ∉ tWords c := by
  simp only [sWords, List.mem_filter, decide_eq_true_eq,
    mem_shortReducedWords_iff]

/-- The **normal-closure derivation** attached to a `T`-word checks: the
decoded product of conjugates of relators and their inverses is the word
itself, in the free group on the code's alphabet. -/
def ExprChecks (P : PresentationCode) (w : List (ℕ × Bool))
    (π : RawCertificate) : Prop :=
  rawValue P π = wordOf P w

instance instDecidableExprChecks (P : PresentationCode)
    (w : List (ℕ × Bool)) (π : RawCertificate) :
    Decidable (ExprChecks P w π) := by
  unfold ExprChecks
  infer_instance

/-- `prop:mf-upper-bound`, proof sentence `a5c1cde4d5f1`: "Such an expression is
checkable, and its existence forces `w = 1` in `G_P`."

Checkability is the `Decidable` instance above --- the check is an equality in
the free group on a finite alphabet.  Soundness is the repository's
`AdianRabinWordProblem.wordProblem_iff_exists_rawCertificate`. -/
theorem wordProblem_of_exprChecks (P : PresentationCode)
    (w : List (ℕ × Bool)) (π : RawCertificate) (h : ExprChecks P w π) :
    WordProblem P w :=
  (wordProblem_iff_exists_rawCertificate P w).2 ⟨π, h⟩

/-- Conversely, a word that dies in `G_P` has such a derivation, so the printed
labelling is always available on the trivial words. -/
theorem exists_exprChecks_of_wordProblem (P : PresentationCode)
    (w : List (ℕ × Bool)) (h : WordProblem P w) :
    ∃ π : RawCertificate, ExprChecks P w π :=
  (wordProblem_iff_exists_rawCertificate P w).1 h

/-- Well-formedness of a certificate at scale `n`: the dimension is at least
one, and every word it labels `T` is a reduced word of length at most `n`
carrying a derivation that checks. -/
def WellFormed (P : PresentationCode) (n : ℕ) (c : PrintedCertificate) : Prop :=
  1 ≤ certDim c ∧
    ∀ z ∈ tEntries c, IsShortReduced P n z.1 ∧ ExprChecks P z.1 z.2

instance instDecidableWellFormed (P : PresentationCode) (n : ℕ)
    (c : PrintedCertificate) : Decidable (WellFormed P n c) := by
  unfold WellFormed
  infer_instance

/-- Every word a well-formed certificate labels `T` is trivial in `G_P`. -/
theorem wordProblem_of_mem_tWords {P : PresentationCode} {n : ℕ}
    {c : PrintedCertificate} (hc : WellFormed P n c) {w : List (ℕ × Bool)}
    (hw : w ∈ tWords c) : WordProblem P w := by
  obtain ⟨z, hz, hzw⟩ := List.mem_map.1 hw
  obtain ⟨-, hcheck⟩ := hc.2 z hz
  rw [← hzw]
  exact wordProblem_of_exprChecks P z.1 z.2 hcheck

/-- A nontrivial short reduced word is labelled `S` by a well-formed
certificate: it cannot be labelled `T`, since a `T`-label carries a
normal-closure derivation. -/
theorem mem_sWords_of_not_wordProblem {P : PresentationCode} {n : ℕ}
    {c : PrintedCertificate} (hc : WellFormed P n c) {w : List (ℕ × Bool)}
    (hshort : IsShortReduced P n w) (hw : ¬ WordProblem P w) :
    w ∈ sWords P n c :=
  (mem_sWords_iff P n c w).2 ⟨hshort, fun hmem => hw
    (wordProblem_of_mem_tWords hc hmem)⟩

/-! ## The matrix condition `Φ` -/

/-- `prop:mf-upper-bound`, proof sentence `4b85128c696d`, last clause: `w(U)` is
"the evaluation of `w` at `U_1, …, U_k` with `x_j^{-1} ↦ U_j^*`". -/
def wordEval {P : PresentationCode} (M : Microstate P) :
    List (ℕ × Bool) → Matrix M.model M.model ℂ
  | [] => 1
  | (i, true) :: rest =>
      (M.gen (letterOf P i) : Matrix M.model M.model ℂ) * wordEval M rest
  | (i, false) :: rest =>
      ((M.gen (letterOf P i) : Matrix M.model M.model ℂ))ᴴ * wordEval M rest

/-- The printed evaluation is the microstate's free-group homomorphism read at
the word.  This is what lets `‖w(U) - 1‖` be measured by `Microstate.len`. -/
theorem wordEval_eq_hom {P : PresentationCode} (M : Microstate P) :
    ∀ w : List (ℕ × Bool),
      wordEval M w =
        ((M.hom (wordOf P w) : Matrix.unitaryGroup M.model ℂ) :
          Matrix M.model M.model ℂ)
  | [] => by
      rw [wordEval, wordOf_nil, map_one]
      rfl
  | (i, true) :: rest => by
      have hgen : M.hom (FreeGroup.of (letterOf P i)) = M.gen (letterOf P i) := by
        show FreeGroup.lift M.gen (FreeGroup.of (letterOf P i)) = _
        apply FreeGroup.lift_apply_of
      rw [wordEval, wordEval_eq_hom M rest, wordOf_cons_pos, map_mul, hgen]
      rfl
  | (i, false) :: rest => by
      have hgen : M.hom (FreeGroup.of (letterOf P i)) = M.gen (letterOf P i) := by
        show FreeGroup.lift M.gen (FreeGroup.of (letterOf P i)) = _
        apply FreeGroup.lift_apply_of
      have hinv : (((M.gen (letterOf P i))⁻¹ :
          Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ)
            = ((M.gen (letterOf P i) : Matrix M.model M.model ℂ))ᴴ := by
        rw [← Matrix.star_eq_conjTranspose]
        rfl
      rw [wordEval, wordEval_eq_hom M rest, wordOf_cons_neg, map_mul, map_inv,
        hgen, ← hinv]
      rfl

/-- The printed quantity `‖w(U) - 1‖` is the microstate displacement of the
word. -/
theorem norm_wordEval_sub_one {P : PresentationCode} (M : Microstate P)
    (w : List (ℕ × Bool)) : ‖wordEval M w - 1‖ = M.len w := by
  rw [wordEval_eq_hom, Microstate.len_def, opLength]

/-- `prop:mf-upper-bound`, proof sentence `4b85128c696d`: "Let `Φ(P,n,c)` be the
statement that there are `U_1, …, U_k ∈ U(d)` with `‖r_i(U) - 1‖ ≤ 2^{-n}` for
`i ≤ m` and `‖w(U) - 1‖ ≥ 1/4` for every word `w` labelled `S`."

A `Microstate P` of dimension `d` is exactly a tuple `U_1, …, U_k ∈ U(d)`, and
`Microstate.len` is exactly `‖w(U) - 1‖` (`norm_wordEval_sub_one`). -/
def PhiSpec (P : PresentationCode) (n : ℕ) (c : PrintedCertificate) : Prop :=
  ∃ M : Microstate P, Fintype.card M.model = certDim c ∧
    (∀ r ∈ P.2, M.len r ≤ (1 / 2 : ℝ) ^ n) ∧
      ∀ w ∈ sWords P n c, (1 / 4 : ℝ) ≤ M.len w

end

end Certificates
end MFRecognition
end Manuscript
end GroupApproximation
