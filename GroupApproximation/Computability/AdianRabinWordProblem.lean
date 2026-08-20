import GroupApproximation.Computability.PresentationCodes

/-!
# Certificates for the word problem of a finite presentation

This module builds the layer the manuscript's undecidability corollary needs
between Mathlib's computability theory and Mathlib's group presentations:
a **finite, code-independent certificate** for the positive instances of the
word problem, and the theorem that the certificates are exactly right.

Manuscript location, by stable anchor (`non_mf_groups_exist.tex` is under
concurrent edit, so no line numbers appear here):
`\subsection{Undecidability of MF recognition}`, the discussion paragraph
beginning "This corollary carries one classical literature input, used only
here".  The sentence certified here is

> The instances with $w=1$ form a recursively enumerable set

which the manuscript uses silently and which is *not* implied by
undecidability of the word problem.  See `AdianRabinMarkovProperty` for the
full ledger; this file closes the mathematical half of item (c) there.

## What is proved

* `exists_list_of_mem_closure` --- membership in a subgroup closure is
  witnessed by a finite list of generators and inverses of generators.
  Mathlib has this for `Submonoid` and `Subring`, but **not** for `Subgroup`,
  so it is proved here from `Subgroup.closure_induction`.
* `mem_normalClosure_iff` --- an element lies in the normal closure of `s`
  exactly when it is a finite product of conjugates of elements of `s` and of
  their inverses.  This is the mathematical content of "the word problem is
  recursively enumerable": the positive instances are exactly those carrying a
  finite certificate.
* `WordProblem` --- the word problem of a `PresentationCodes.PresentationCode`,
  stated as triviality in `PresentationCodes.Carrier`.
* `RawCertificate` --- a `Primcodable` certificate type carrying no dependent
  data, together with its decoding `rawValue`.
* `wordProblem_iff_exists_rawCertificate` --- **the main theorem.** A coded
  word dies in the coded group exactly when some raw certificate decodes to
  it.
* `wordProblemPred` --- the same predicate packaged on the `Primcodable` type
  `PresentationCode × List (ℕ × Bool)`, i.e. in the slot that
  `MarkovMFConsequences.AdianRabinReduction` leaves open as `sourceProperty`.

Deduplication note for integration: `PresentationCodeCompleteness` proves
`wordOf_encodeWord`, which yields surjectivity of `wordOf` in a different
form.  `wordOf_surjective` below is kept separate so that this module depends
only on `PresentationCodes`, but the two can be merged once both files are
green.

## Why the certificate has to be raw

A certificate for `w = 1` naturally consists of free-group elements: the
conjugators and the relators.  But `PresentationCodes.wordOf c` lands in
`FreeGroup (Fin (genCount c))`, a type that **depends on the code `c`**.  A
dependent type has no `Primcodable` instance and cannot have one, so a search
space of free-group certificates is not a search space a partial recursive
function can range over.

Hence `RawCertificate` is `List (List (ℕ × Bool) × List (ℕ × Bool) × Bool)`:
lists of (conjugator word, relator word, sign), all code-independent raw data.
Decoding is total, by two deliberate choices mirroring the ones in
`PresentationCodes`:

* letters are read modulo the alphabet size (already true of `wordOf`); and
* a relator word that the code does not list decodes to `1` rather than to
  garbage (`relatorOf`).

The second choice is what makes soundness (`rawValue_mem_normalClosure`)
unconditional: every decoded factor lies in the normal closure whether or not
the certificate is well-formed, so a search over *all* certificates can only
ever produce genuine positive instances.

## What remains before r.e.-ness itself

Exactly one obligation, and it is plumbing rather than mathematics:

> `ComputablePred fun x : PresentationCode × List (ℕ × Bool) × RawCertificate ↦
>   rawValue x.1 x.2.2 = wordOf x.1 x.2.1`

Given that, `REPred (fun x : PresentationCode × List (ℕ × Bool) ↦
WordProblem x.1 x.2)` follows from `wordProblem_iff_exists_rawCertificate` by
an unbounded search, and the manuscript's sentence is discharged.

The obligation is not reachable at this Mathlib revision without new work,
because `FreeGroup` has no `Primrec` API at all: there is no `Primcodable`
instance for `FreeGroup α`, and free reduction (`FreeGroup.reduce`,
`FreeGroup.toWord`) has no primitive-recursiveness lemma.  Two routes:

1. **Encode free-group elements.**  Build `Primcodable (FreeGroup (Fin n))`
   through `FreeGroup.toWord`/`FreeGroup.mk_toWord`, then prove
   `Primrec FreeGroup.reduce`.  This still leaves the dependent-type problem
   above for the *value* type, so it only works after fixing the alphabet.
2. **Stay on raw words** (recommended).  Replace the equality test
   `rawValue c cert = wordOf c w` by a purely syntactic one: concatenate the
   decoded blocks and the inverse of `w` into a single raw word, and let the
   certificate additionally carry the list of positions at which adjacent
   inverse letters are cancelled.  Checking a deletion sequence uses only
   `List.take`, `List.drop`, `List.append` and decidable equality, all of which
   Mathlib's `Primrec` list API reaches, and free reduction is confluent and
   terminating so the certificate always exists.  The extra mathematics is the
   equivalence "freely trivial iff some deletion sequence reaches `[]`", which
   is `FreeGroup.Red` theory.

Estimated remaining size for route 2: **~250--450 lines**, no mathematical
risk, entirely `Primrec` bookkeeping plus the `Red`-theory equivalence.  That
is the whole of item (c); items (a) Adian--Rabin and (b) Novikov--Boone are
untouched by this file and remain as assessed in `AdianRabinMarkovProperty`.
-/

namespace GroupApproximation
namespace AdianRabinWordProblem

open PresentationCodes

universe u

/-! ## Finite products certify subgroup-closure membership -/

section Closure

variable {G : Type u} [Group G]

/-- A finite product of conjugates of elements of `s` and of their inverses
lies in the normal closure of `s`. -/
theorem list_prod_mem_normalClosure {s : Set G} :
    ∀ l : List G,
      (∀ y ∈ l, ∃ g : G, ∃ r ∈ s, y = g * r * g⁻¹ ∨ y = g * r⁻¹ * g⁻¹) →
        l.prod ∈ Subgroup.normalClosure s
  | [], _ => by simp
  | a :: t, hl => by
      rw [List.prod_cons]
      have ha : a ∈ Subgroup.normalClosure s := by
        obtain ⟨g, r, hr, hcase⟩ := hl a (by simp)
        have hconj : g * r * g⁻¹ ∈ Subgroup.normalClosure s :=
          Subgroup.conjugatesOfSet_subset_normalClosure
            (Group.mem_conjugatesOfSet_iff.2 ⟨r, hr, isConj_iff.2 ⟨g, rfl⟩⟩)
        rcases hcase with h | h
        · rw [h]
          exact hconj
        · rw [h, ← conj_inv]
          exact inv_mem hconj
      exact mul_mem ha
        (list_prod_mem_normalClosure t fun y hy ↦ hl y (by simp [hy]))

/-- Membership in a subgroup closure is witnessed by a finite list of
generators and inverses of generators.

Mathlib proves this for `Submonoid` (`Submonoid.exists_list_of_mem_closure`)
and for `Subring`, but not for `Subgroup`, so it is derived here from
`Subgroup.closure_induction`. -/
theorem exists_list_of_mem_closure {s : Set G} {x : G}
    (hx : x ∈ Subgroup.closure s) :
    ∃ l : List G, (∀ y ∈ l, y ∈ s ∨ y⁻¹ ∈ s) ∧ l.prod = x := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    refine ⟨[y], ?_, by simp⟩
    intro z hz
    rw [List.mem_singleton] at hz
    subst hz
    exact Or.inl hy
  · exact ⟨[], by simp, by simp⟩
  · rintro a b _ _ ⟨la, hla, rfl⟩ ⟨lb, hlb, rfl⟩
    refine ⟨la ++ lb, ?_, by rw [List.prod_append]⟩
    intro y hy
    rcases List.mem_append.1 hy with h | h
    · exact hla y h
    · exact hlb y h
  · rintro a _ ⟨l, hl, rfl⟩
    refine ⟨(l.map fun z ↦ z⁻¹).reverse, ?_, (List.prod_inv_reverse l).symm⟩
    intro y hy
    rw [List.mem_reverse, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rcases hl z hz with h | h
    · exact Or.inr (by simpa using h)
    · exact Or.inl h

/-- **Certificate characterization of the normal closure.**

An element lies in the normal closure of `s` exactly when it is a finite
product of conjugates of elements of `s` and of their inverses.  Read at a
group presentation, this says that the positive instances of the word problem
are exactly the ones carrying a finite certificate --- the mathematical
content of the manuscript's "the instances with `w = 1` form a recursively
enumerable set". -/
theorem mem_normalClosure_iff {s : Set G} {x : G} :
    x ∈ Subgroup.normalClosure s ↔
      ∃ l : List G,
        (∀ y ∈ l, ∃ g : G, ∃ r ∈ s, y = g * r * g⁻¹ ∨ y = g * r⁻¹ * g⁻¹) ∧
          l.prod = x := by
  constructor
  · intro hx
    have hx' : x ∈ Subgroup.closure (Group.conjugatesOfSet s) := hx
    obtain ⟨l, hl, hprod⟩ := exists_list_of_mem_closure hx'
    refine ⟨l, ?_, hprod⟩
    intro y hy
    rcases hl y hy with h | h
    · obtain ⟨r, hr, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 h
      obtain ⟨g, hg⟩ := isConj_iff.1 hconj
      exact ⟨g, r, hr, Or.inl hg.symm⟩
    · obtain ⟨r, hr, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 h
      obtain ⟨g, hg⟩ := isConj_iff.1 hconj
      refine ⟨g, r, hr, Or.inr ?_⟩
      have hy' : (g * r * g⁻¹)⁻¹ = y := by rw [hg, inv_inv]
      rw [← hy']
      exact conj_inv
  · rintro ⟨l, hl, rfl⟩
    exact list_prod_mem_normalClosure l hl

end Closure

/-! ## The relator set of a presentation code -/

/-- The relator set named by a code, as a `Set` in the free group on the
code's alphabet.  This is definitionally the relator set that
`PresentationCodes.Carrier` quotients by. -/
abbrev relatorSet (c : PresentationCode) : Set (FreeGroup (Fin (genCount c))) :=
  (relatorFinset c : Set (FreeGroup (Fin (genCount c))))

/-- A free-group element is a coded relator exactly when it is the value of a
raw relator word listed by the code. -/
theorem mem_relatorSet_iff {c : PresentationCode}
    {r : FreeGroup (Fin (genCount c))} :
    r ∈ relatorSet c ↔ ∃ u ∈ c.2, wordOf c u = r := by
  simp only [relatorSet, relatorFinset, Finset.mem_coe, List.mem_toFinset,
    List.mem_map]

/-- A listed relator word names an element of the relator set. -/
theorem wordOf_mem_relatorSet {c : PresentationCode} {u : List (ℕ × Bool)}
    (hu : u ∈ c.2) : wordOf c u ∈ relatorSet c :=
  mem_relatorSet_iff.2 ⟨u, hu, rfl⟩

/-! ## Raw words exhaust the free group on a coded alphabet -/

/-- Reading a coded letter as a natural number and decoding it again is the
identity, because a letter index below the alphabet size is unchanged by
reduction modulo that size. -/
theorem map_letterOf_map_val (c : PresentationCode) :
    ∀ L : List (Fin (genCount c) × Bool),
      (L.map fun p ↦ ((p.1 : ℕ), p.2)).map
          (fun q : ℕ × Bool ↦ (letterOf c q.1, q.2)) = L
  | [] => by simp
  | p :: t => by
      have hlt : (p.1 : ℕ) < genCount c := p.1.isLt
      have ih := map_letterOf_map_val c t
      simp only [List.map_cons, List.map_map] at ih ⊢
      rw [ih]
      simp [letterOf, Nat.mod_eq_of_lt hlt]

/-- Every element of the free group on a code's alphabet is the value of some
raw word.  This is what lets a certificate carry its conjugators as raw data
instead of as free-group elements. -/
theorem wordOf_surjective (c : PresentationCode) :
    Function.Surjective (wordOf c) := by
  intro x
  refine ⟨(FreeGroup.toWord x).map fun p ↦ ((p.1 : ℕ), p.2), ?_⟩
  simp only [wordOf]
  rw [map_letterOf_map_val c (FreeGroup.toWord x), FreeGroup.mk_toWord]

/-! ## The word problem and its raw certificates -/

/-- The word problem of a presentation code: does the coded word die in the
coded group?  The ascription to `PresentationCodes.Carrier` is what ties this
predicate to the coded semantics rather than to a re-derived one. -/
def WordProblem (c : PresentationCode) (w : List (ℕ × Bool)) : Prop :=
  (PresentedGroup.mk (relatorSet c) (wordOf c w) : Carrier c) = 1

/-- A raw certificate: a finite list of triples (conjugator word, relator
word, sign).  Every component is code-independent raw data, so the type is
`Primcodable`; see the module docstring for why a certificate of free-group
elements could not be. -/
abbrev RawCertificate : Type :=
  List (List (ℕ × Bool) × List (ℕ × Bool) × Bool)

/-- Raw certificates are a recursive datatype. -/
example : Primcodable RawCertificate := inferInstance

/-- Code, word and certificate jointly form a `Primcodable` search space:
this is the space an r.e.-ness proof for the word problem quantifies over. -/
example :
    Primcodable (PresentationCode × List (ℕ × Bool) × RawCertificate) :=
  inferInstance

/-- The relator named by a raw word: its value when the code lists that word,
and `1` otherwise.  Totalizing this way keeps decoding a plain function and
keeps every decoded factor inside the normal closure, so a search over
malformed certificates cannot produce a false positive. -/
def relatorOf (c : PresentationCode) (u : List (ℕ × Bool)) :
    FreeGroup (Fin (genCount c)) :=
  if u ∈ c.2 then wordOf c u else 1

/-- Decoded value of one certificate entry: the conjugate of the named
relator, inverted when the sign bit is `false`. -/
def rawFactor (c : PresentationCode)
    (t : List (ℕ × Bool) × List (ℕ × Bool) × Bool) :
    FreeGroup (Fin (genCount c)) :=
  wordOf c t.1 *
    (if t.2.2 then relatorOf c t.2.1 else (relatorOf c t.2.1)⁻¹) *
      (wordOf c t.1)⁻¹

/-- Decoded value of a whole certificate. -/
def rawValue (c : PresentationCode) (cert : RawCertificate) :
    FreeGroup (Fin (genCount c)) :=
  (cert.map (rawFactor c)).prod

/-- The empty certificate decodes to the identity. -/
theorem rawValue_nil (c : PresentationCode) : rawValue c [] = 1 := by
  simp [rawValue]

/-- Decoding a certificate is multiplicative over `cons`. -/
theorem rawValue_cons (c : PresentationCode)
    (t : List (ℕ × Bool) × List (ℕ × Bool) × Bool) (cert : RawCertificate) :
    rawValue c (t :: cert) = rawFactor c t * rawValue c cert := by
  simp [rawValue]

/-- Every decoded relator lies in the normal closure of the coded relators,
whether or not the raw word is one the code lists. -/
theorem relatorOf_mem_normalClosure (c : PresentationCode)
    (u : List (ℕ × Bool)) :
    relatorOf c u ∈ Subgroup.normalClosure (relatorSet c) := by
  by_cases hu : u ∈ c.2
  · rw [relatorOf, if_pos hu]
    exact Subgroup.subset_normalClosure (wordOf_mem_relatorSet hu)
  · rw [relatorOf, if_neg hu]
    exact one_mem _

/-- Every decoded certificate entry lies in the normal closure.  An entry
naming a word the code does not list contributes the identity, which is why no
normality argument is needed: each factor is either a conjugate of a genuine
relator, the inverse of one, or `1`. -/
theorem rawFactor_mem_normalClosure (c : PresentationCode)
    (t : List (ℕ × Bool) × List (ℕ × Bool) × Bool) :
    rawFactor c t ∈ Subgroup.normalClosure (relatorSet c) := by
  by_cases hu : t.2.1 ∈ c.2
  · have hconj :
        wordOf c t.1 * wordOf c t.2.1 * (wordOf c t.1)⁻¹ ∈
          Subgroup.normalClosure (relatorSet c) :=
      Subgroup.conjugatesOfSet_subset_normalClosure
        (Group.mem_conjugatesOfSet_iff.2
          ⟨wordOf c t.2.1, wordOf_mem_relatorSet hu,
            isConj_iff.2 ⟨wordOf c t.1, rfl⟩⟩)
    rw [rawFactor, relatorOf, if_pos hu]
    split
    · exact hconj
    · rw [← conj_inv]
      exact inv_mem hconj
  · have hz : rawFactor c t = 1 := by
      rw [rawFactor, relatorOf, if_neg hu]
      split <;> simp
    rw [hz]
    exact one_mem _

/-- **Soundness of raw certificates.**  Every certificate, well-formed or not,
decodes to an element of the normal closure of the coded relators. -/
theorem rawValue_mem_normalClosure (c : PresentationCode) :
    ∀ cert : RawCertificate,
      rawValue c cert ∈ Subgroup.normalClosure (relatorSet c)
  | [] => by
      rw [rawValue_nil]
      exact one_mem _
  | t :: rest => by
      rw [rawValue_cons]
      exact mul_mem (rawFactor_mem_normalClosure c t)
        (rawValue_mem_normalClosure c rest)

/-- **Completeness of raw certificates.**  Every finite product of conjugates
of coded relators and of their inverses is the value of a raw certificate. -/
theorem exists_rawCertificate (c : PresentationCode) :
    ∀ l : List (FreeGroup (Fin (genCount c))),
      (∀ y ∈ l, ∃ g : FreeGroup (Fin (genCount c)), ∃ r ∈ relatorSet c,
          y = g * r * g⁻¹ ∨ y = g * r⁻¹ * g⁻¹) →
        ∃ cert : RawCertificate, rawValue c cert = l.prod
  | [], _ => ⟨[], by rw [rawValue_nil, List.prod_nil]⟩
  | a :: t, hl => by
      obtain ⟨cert, hcert⟩ :=
        exists_rawCertificate c t fun y hy ↦ hl y (by simp [hy])
      obtain ⟨g, r, hr, hcase⟩ := hl a (by simp)
      obtain ⟨u, hu, hru⟩ := mem_relatorSet_iff.1 hr
      obtain ⟨gw, hgw⟩ := wordOf_surjective c g
      have hrel : relatorOf c u = r := by rw [relatorOf, if_pos hu, hru]
      rcases hcase with h | h
      · refine ⟨(gw, u, true) :: cert, ?_⟩
        have hfac : rawFactor c (gw, u, true) = a := by
          have hexp : rawFactor c (gw, u, true)
              = wordOf c gw * relatorOf c u * (wordOf c gw)⁻¹ := by
            simp [rawFactor]
          rw [hexp, hgw, hrel, h]
        rw [rawValue_cons, hfac, hcert, List.prod_cons]
      · refine ⟨(gw, u, false) :: cert, ?_⟩
        have hfac : rawFactor c (gw, u, false) = a := by
          have hexp : rawFactor c (gw, u, false)
              = wordOf c gw * (relatorOf c u)⁻¹ * (wordOf c gw)⁻¹ := by
            simp [rawFactor]
          rw [hexp, hgw, hrel, h]
        rw [rawValue_cons, hfac, hcert, List.prod_cons]

/-- **The word problem of a presentation code, certified.**

A coded word dies in the coded group exactly when some raw certificate decodes
to it.  Since `RawCertificate` is `Primcodable`, this reduces recursive
enumerability of the word problem to computability of the decoding map, which
is the sole remaining obligation described in the module docstring.

This is the manuscript's step "the instances with `w = 1` form a recursively
enumerable set", supplied in the only form that a partial recursive function
can search: an existential over code-independent finite data. -/
theorem wordProblem_iff_exists_rawCertificate (c : PresentationCode)
    (w : List (ℕ × Bool)) :
    WordProblem c w ↔ ∃ cert : RawCertificate, rawValue c cert = wordOf c w := by
  constructor
  · intro hw
    have hmem : wordOf c w ∈ Subgroup.normalClosure (relatorSet c) :=
      PresentedGroup.mk_eq_one_iff.1 hw
    obtain ⟨l, hl, hprod⟩ := mem_normalClosure_iff.1 hmem
    obtain ⟨cert, hcert⟩ := exists_rawCertificate c l hl
    exact ⟨cert, by rw [hcert, hprod]⟩
  · rintro ⟨cert, hcert⟩
    refine PresentedGroup.mk_eq_one_iff.2 ?_
    rw [← hcert]
    exact rawValue_mem_normalClosure c cert

/-! ## The word problem as the reduction's source predicate

`MarkovMFConsequences.AdianRabinReduction` is quantified over an abstract
`sourceProperty` on an abstract `Primcodable` type.  `PresentationCodes` gave
the *target* side a concrete referent; the definitions here do the same for the
*source* side, so that the reduction's two remaining obligations can be stated
in fully concrete terms rather than as parameters.  Neither definition
discharges anything: naming a predicate is not proving a theorem about it. -/

/-- The source side of the reduction is a `Primcodable` decision problem. -/
example : Primcodable (PresentationCode × List (ℕ × Bool)) := inferInstance

/-- The word problem as a predicate on a `Primcodable` type: given a finite
presentation code and a raw word, does the word die in the presented group?

Docking this into `MarkovMFConsequences.AdianRabinReduction` as
`sourceProperty` turns the abstract hypothesis `¬ComputablePred sourceProperty`
into the literal Novikov--Boone statement, exactly as
`PresentationCodes.semantics` turned the target side into literal MF
recognition. -/
def wordProblemPred : PresentationCode × List (ℕ × Bool) → Prop :=
  fun x ↦ WordProblem x.1 x.2

/-- The certificate characterization, restated for the packaged source
predicate.  This is the shape an r.e.-ness proof consumes: an existential over
a `Primcodable` type, with the matrix a decidable equation once the decoding
map is known to be computable. -/
theorem wordProblemPred_iff (x : PresentationCode × List (ℕ × Bool)) :
    wordProblemPred x ↔
      ∃ cert : RawCertificate, rawValue x.1 cert = wordOf x.1 x.2 :=
  wordProblem_iff_exists_rawCertificate x.1 x.2

end AdianRabinWordProblem
end GroupApproximation
