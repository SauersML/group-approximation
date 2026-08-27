import GroupApproximation.Computability.RawWord
import GroupApproximation.Computability.RawTransformPrimrec
import GroupApproximation.Computability.AdianRabinWordProblem
import GroupApproximation.Computability.CodedWordTriviality
import GroupApproximation.Computability.AdianRabinMarkovProperty
import GroupApproximation.Computability.AdianRabinVariantTransform
import GroupApproximation.Computability.BooneWordProblemUndecidable
import Mathlib.Computability.RE

/-!
# The word problem on codes is recursively enumerable

`AdianRabinWordProblem` reduced the positive side of the word problem to a
search over a `Primcodable` certificate type, and then recorded the obligation
it could not discharge: its matrix,

    rawValue c cert = wordOf c w,

is an equation in `FreeGroup (Fin (genCount c))`, a type that *depends on the
code*, so no partial recursive function can evaluate it.  That module's docstring
names the intended repair --- "stay on raw words" --- and this file carries it
out.

The repair is that both sides of the matrix are values of raw words.  The
certificate's decoded value is `wordOf c` of a raw word built from the
certificate by concatenation alone (`certWord`), so the matrix becomes triviality
of a single raw word, `certWord c cert ++ invWord w`, and
`CodedWordTriviality.wordOf_eq_one_iff_exists_steps` turns *that* into a second
existential over deletion certificates --- again raw data.  Pairing the two
existentials gives one search over `RawCertificate × List ℕ` whose matrix is a
decidable equation between `Option (List (ℕ × Bool))`s.  No free-group element
and no dependent type survives into the search space.

The one place where the code re-enters is `relatorOf`, which reads a raw word as
a relator only when the code lists it.  That test is list membership, for which
pinned Mathlib carries no `Primrec` fact; `PrimrecRel.exists_mem_list` applied to
`Primrec.eq` supplies one through `∃ a ∈ L, a = u`.

## What this closes

The manuscript's `cor:undecidable` discussion asserts that the instances with
`w = 1` form a recursively enumerable set, and uses it to conclude that the
instances with `w ≠ 1` do not.  `rePred_wordProblemPred` is the first half.  The
second is Post's theorem run against `D4'`; since `D4'` carries no hypothesis and
no literature input, neither does `not_rePred_compl_wordProblemPred`, and
`operatorMF_negative_side_not_re` carries it across the Adian--Rabin reduction to
MF recognition itself.  Both clauses are closed unconditionally.
-/

namespace GroupApproximation
namespace WordProblemRE

open PresentationCodes RawWord AdianRabinWordProblem

/-! ## The certificate, as a raw word

Every value a certificate decodes to is `wordOf c` of a raw word.  Building that
word is the whole content of the reduction: once it exists, the matrix of the
search is triviality of a single raw word, and triviality of a raw word is
already known to be a search over raw data. -/

/-- The raw word naming one certificate entry's relator, signed.  A relator word
the code does not list contributes the empty word, mirroring `relatorOf`'s
totalisation --- which is what keeps the search sound over malformed
certificates. -/
def relatorWord (c : PresentationCode) (u : List (ℕ × Bool)) (s : Bool) :
    List (ℕ × Bool) :=
  if u ∈ c.2 then (bif s then u else invWord u) else []

theorem wordOf_relatorWord (c : PresentationCode) (u : List (ℕ × Bool)) (s : Bool) :
    wordOf c (relatorWord c u s)
      = (if s then relatorOf c u else (relatorOf c u)⁻¹) := by
  by_cases hu : u ∈ c.2 <;> cases s <;>
    simp [relatorWord, relatorOf, hu, wordOf_invWord, -wordOf_def]

/-- The raw word naming one certificate entry: conjugator, signed relator,
inverse conjugator. -/
def factorWord (c : PresentationCode)
    (t : List (ℕ × Bool) × List (ℕ × Bool) × Bool) : List (ℕ × Bool) :=
  t.1 ++ relatorWord c t.2.1 t.2.2 ++ invWord t.1

theorem wordOf_factorWord (c : PresentationCode)
    (t : List (ℕ × Bool) × List (ℕ × Bool) × Bool) :
    wordOf c (factorWord c t) = rawFactor c t := by
  rw [factorWord, wordOf_append, wordOf_append, wordOf_invWord, wordOf_relatorWord,
    rawFactor]

/-- **The certificate, as a raw word.**  Concatenating the entries' words. -/
def certWord (c : PresentationCode) (cert : RawCertificate) : List (ℕ × Bool) :=
  (cert.map (factorWord c)).flatten

/-- The two recursion equations of `certWord`.  Both are definitional; they are
stated, and stated as `@[simp]` lemmas, because `rw` needs a syntactic target
and the `flatten`-of-`map` form does not present one.  The recursive occurrence
is at a strictly shorter certificate, so the pair terminates. -/
@[simp] theorem certWord_nil (c : PresentationCode) : certWord c [] = [] := rfl

@[simp] theorem certWord_cons (c : PresentationCode)
    (t : List (ℕ × Bool) × List (ℕ × Bool) × Bool) (rest : RawCertificate) :
    certWord c (t :: rest) = factorWord c t ++ certWord c rest := rfl

/-- **The decoded certificate is the value of a raw word.**  This is the step
`AdianRabinWordProblem` left open: the dependent-typed value on the right is
named by the code-independent data on the left. -/
theorem wordOf_certWord (c : PresentationCode) :
    ∀ cert : RawCertificate, wordOf c (certWord c cert) = rawValue c cert
  | [] => by rw [certWord_nil, wordOf_nil, rawValue_nil]
  | t :: rest => by
      rw [certWord_cons, wordOf_append, wordOf_factorWord, rawValue_cons,
        wordOf_certWord c rest]

/-- The single raw word whose triviality is the certificate's correctness. -/
def testWord (c : PresentationCode) (w : List (ℕ × Bool)) (cert : RawCertificate) :
    List (ℕ × Bool) :=
  certWord c cert ++ invWord w

theorem wordOf_testWord_eq_one_iff (c : PresentationCode) (w : List (ℕ × Bool))
    (cert : RawCertificate) :
    wordOf c (testWord c w cert) = 1 ↔ rawValue c cert = wordOf c w := by
  rw [testWord, wordOf_append, wordOf_invWord, wordOf_certWord, mul_inv_eq_one]

/-! ## One search space

The relator certificate and the deletion certificate are two existentials over
`Primcodable` types, so they pair into one.  Deciding the inner existential is
not attempted and is not needed: an r.e.-ness proof only has to search. -/

/-- The search space: a relator certificate together with a deletion certificate
for the raw word it produces. -/
abbrev SearchData : Type := RawCertificate × List ℕ

/-- The matrix of the search: a decidable equation between raw data. -/
def searchCheck (x : PresentationCode × List (ℕ × Bool)) (p : SearchData) : Bool :=
  decide (Computability.applySteps
    (Computability.normLetters x.1 (testWord x.1 x.2 p.1)) p.2 = some [])

theorem searchCheck_eq_true_iff (x : PresentationCode × List (ℕ × Bool))
    (p : SearchData) :
    searchCheck x p = true
      ↔ Computability.applySteps
          (Computability.normLetters x.1 (testWord x.1 x.2 p.1)) p.2 = some [] := by
  simp [searchCheck]

/-- **The word problem, as one search over raw data.**  The right-hand side
quantifies over a `Primcodable` type and its matrix is a `Bool`. -/
theorem wordProblemPred_iff_exists (x : PresentationCode × List (ℕ × Bool)) :
    wordProblemPred x ↔ ∃ p : SearchData, searchCheck x p = true := by
  rw [wordProblemPred_iff]
  constructor
  · rintro ⟨cert, hcert⟩
    obtain ⟨is, his⟩ :=
      (Computability.wordOf_eq_one_iff_exists_steps x.1 (testWord x.1 x.2 cert)).1
        ((wordOf_testWord_eq_one_iff x.1 x.2 cert).2 hcert)
    exact ⟨(cert, is), (searchCheck_eq_true_iff x (cert, is)).2 his⟩
  · rintro ⟨⟨cert, is⟩, h⟩
    refine ⟨cert, (wordOf_testWord_eq_one_iff x.1 x.2 cert).1 ?_⟩
    exact (Computability.wordOf_eq_one_iff_exists_steps x.1 (testWord x.1 x.2 cert)).2
      ⟨is, (searchCheck_eq_true_iff x (cert, is)).1 h⟩

/-! ## The matrix is computable

Every step is list surgery over `Primcodable` types.  The generator indices, the
relator list and the code's alphabet size all enter only as arguments, so nothing
here needs a code to be evaluated. -/

/-- Membership of a raw word in a code's relator list is a primitive recursive
test.  Pinned Mathlib has no `Primrec` fact for list membership; reading `u ∈ L`
as `∃ a ∈ L, a = u` puts it inside `PrimrecRel.exists_mem_list`. -/
theorem primrecPred_mem_relators :
    PrimrecPred fun z : PresentationCode × List (ℕ × Bool) => z.2 ∈ z.1.2 := by
  have h : PrimrecRel fun (L : List (List (ℕ × Bool))) (u : List (ℕ × Bool)) =>
      ∃ a ∈ L, a = u := PrimrecRel.exists_mem_list Primrec.eq
  refine (h.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).of_eq fun z => ?_
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hz
    exact ⟨z.2, hz, rfl⟩

theorem primrec_factorWord : Primrec₂ factorWord := by
  have ht1 : Primrec fun z : PresentationCode ×
      (List (ℕ × Bool) × List (ℕ × Bool) × Bool) => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hu : Primrec fun z : PresentationCode ×
      (List (ℕ × Bool) × List (ℕ × Bool) × Bool) => z.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec fun z : PresentationCode ×
      (List (ℕ × Bool) × List (ℕ × Bool) × Bool) => z.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hmem : PrimrecPred fun z : PresentationCode ×
      (List (ℕ × Bool) × List (ℕ × Bool) × Bool) => z.2.2.1 ∈ z.1.2 :=
    (primrecPred_mem_relators.comp (Primrec.pair Primrec.fst hu)).of_eq fun _ => Iff.rfl
  have hrel0 : Primrec fun z : PresentationCode ×
      (List (ℕ × Bool) × List (ℕ × Bool) × Bool) =>
        (if z.2.2.1 ∈ z.1.2 then (bif z.2.2.2 then z.2.2.1 else invWord z.2.2.1)
          else ([] : List (ℕ × Bool))) :=
    Primrec.ite hmem
      (Primrec.cond hs hu (RawTransformPrimrec.primrec_invWord.comp hu))
      (Primrec.const ([] : List (ℕ × Bool)))
  have hrel : Primrec fun z : PresentationCode ×
      (List (ℕ × Bool) × List (ℕ × Bool) × Bool) =>
        relatorWord z.1 z.2.2.1 z.2.2.2 :=
    hrel0.of_eq fun _ => rfl
  exact (Primrec.list_append.comp (Primrec.list_append.comp ht1 hrel)
    (RawTransformPrimrec.primrec_invWord.comp ht1)).of_eq fun _ => rfl

theorem primrec_certWord : Primrec₂ certWord :=
  (Primrec.list_flatten.comp
    (Primrec.list_map Primrec.snd
      (primrec_factorWord.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)).of_eq
    fun _ => rfl

theorem primrec_searchCheck :
    Primrec₂ searchCheck := by
  have hc : Primrec fun z : (PresentationCode × List (ℕ × Bool)) × SearchData =>
      z.1.1 := Primrec.fst.comp Primrec.fst
  have hw : Primrec fun z : (PresentationCode × List (ℕ × Bool)) × SearchData =>
      z.1.2 := Primrec.snd.comp Primrec.fst
  have hcert : Primrec fun z : (PresentationCode × List (ℕ × Bool)) × SearchData =>
      z.2.1 := Primrec.fst.comp Primrec.snd
  have his : Primrec fun z : (PresentationCode × List (ℕ × Bool)) × SearchData =>
      z.2.2 := Primrec.snd.comp Primrec.snd
  have htest : Primrec fun z : (PresentationCode × List (ℕ × Bool)) × SearchData =>
      testWord z.1.1 z.1.2 z.2.1 :=
    (Primrec.list_append.comp (primrec_certWord.comp hc hcert)
      (RawTransformPrimrec.primrec_invWord.comp hw)).of_eq fun _ => rfl
  have happly : Primrec fun z : (PresentationCode × List (ℕ × Bool)) × SearchData =>
      Computability.applySteps
        (Computability.normLetters z.1.1 (testWord z.1.1 z.1.2 z.2.1)) z.2.2 :=
    Computability.primrec_applySteps.comp
      (Computability.primrec_normLetters.comp hc htest) his
  exact (Primrec.eq.comp happly (Primrec.const (some []))).decide

theorem computable_searchCheck : Computable₂ searchCheck :=
  primrec_searchCheck.to_comp

/-! ## Unbounded search

Pinned Mathlib has `Partrec.dom_re` and `Partrec.rfindOpt` but no packaging of
the two into "an existential over a `Primcodable` type with a computable matrix
is r.e.".  The search is therefore spelled out: run through `ℕ`, decode each
number into the search space, and halt at the first decoded witness the matrix
accepts.  Decoding is total and `Encodable.encodek` makes it surjective, which is
what makes the search find every witness. -/

/-- **Unbounded search.**  A predicate cut out by an existential over a
`Primcodable` type with a computable `Bool` matrix is recursively enumerable. -/
theorem rePred_exists_eq_true {α β : Type} [Primcodable α] [Primcodable β]
    {g : α → β → Bool} (hg : Computable₂ g) :
    REPred fun a : α => ∃ b : β, g a b = true := by
  have hstep : Computable₂ fun (a : α) (n : ℕ) =>
      (Encodable.decode (α := β) n).bind fun b => bif g a b then some b else none := by
    refine Computable.option_bind (Computable.decode.comp Computable.snd) ?_
    exact Computable.cond (hg.comp (Computable.fst.comp Computable.fst) Computable.snd)
      (Computable.option_some.comp Computable.snd)
      (Computable.const (none : Option β))
  refine (Partrec.rfindOpt hstep).dom_re.of_eq fun a => ?_
  rw [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨n, b, hb⟩
    cases hd : (Encodable.decode (α := β) n) with
    | none => simp [hd] at hb
    | some b' =>
        cases hv : g a b' with
        | false => simp [hd, hv] at hb
        | true => exact ⟨b', hv⟩
  · rintro ⟨b, hb⟩
    exact ⟨Encodable.encode b, b, by simp [Encodable.encodek, hb]⟩

/-! ## The theorem -/

/-- **The word problem on presentation codes is recursively enumerable.**

This is the manuscript's sentence "the instances with `w = 1` form a recursively
enumerable set", with no hypothesis: the certificate characterisation is
`AdianRabinWordProblem.wordProblemPred_iff`, its matrix is made raw above, and
the resulting search is one unbounded search over `Primcodable` data. -/
theorem rePred_wordProblemPred : REPred AdianRabinWordProblem.wordProblemPred :=
  (rePred_exists_eq_true computable_searchCheck).of_eq fun x =>
    (wordProblemPred_iff_exists x).symm

/-! ## The negative side

Post's theorem turns r.e.-ness of the positive side plus undecidability into
non-r.e.-ness of the negative side.  The undecidability is `D4'`, which is itself
unconditional, so the conclusions are too.

The hypothesis-taking forms come first, and are kept, because they record which
half of the corollary needs what: the positive side is r.e. outright, and only
the negative side reaches for `D4'`.  Reading the two off a single statement
would hide that. -/

/-- **The negative side of the word problem is not recursively enumerable**,
given that the word problem is undecidable.  This is the manuscript's inference
"an enumeration of the non-MF presentations would enumerate that set, making the
word problem decidable", contraposed. -/
theorem not_rePred_compl_wordProblemPred_of_not_computablePred
    (h : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ REPred fun x => ¬ AdianRabinWordProblem.wordProblemPred x := fun hre =>
  h (AdianRabinMarkovProperty.computablePred_of_re_of_negativeSide_re
    rePred_wordProblemPred hre)

/-- **The negative side of operator-MF recognition is not recursively
enumerable**, given undecidability of the word problem.  One application of the
Adian--Rabin reduction to the previous theorem. -/
theorem operatorMF_negative_side_not_re_of_not_computablePred
    (h : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ REPred fun code =>
      ¬ MarkovMFConsequences.operatorMFProperty PresentationCodes.semantics code :=
  AdianRabinVariantTransform.operatorMF_negative_side_not_re_of_wordProblem
    (not_rePred_compl_wordProblemPred_of_not_computablePred h)

/-- **The negative side of the word problem is not recursively enumerable.**

Unconditional: the positive side is `rePred_wordProblemPred` above, and the
undecidability Post's theorem needs against it is `D4'`, which carries no
hypothesis and no literature input.  This is the second clause of the
manuscript's `cor:undecidable` discussion. -/
theorem not_rePred_compl_wordProblemPred :
    ¬ REPred fun x => ¬ AdianRabinWordProblem.wordProblemPred x :=
  not_rePred_compl_wordProblemPred_of_not_computablePred
    Computability.not_computablePred_wordProblemPred

/-- **The negative side of operator-MF recognition is not recursively
enumerable.**  Unconditional, by the same route through the Adian--Rabin
reduction: no enumeration lists the presentation codes whose group is not
operator-MF. -/
theorem operatorMF_negative_side_not_re :
    ¬ REPred fun code =>
      ¬ MarkovMFConsequences.operatorMFProperty PresentationCodes.semantics code :=
  operatorMF_negative_side_not_re_of_not_computablePred
    Computability.not_computablePred_wordProblemPred

end WordProblemRE
end GroupApproximation
