import GroupApproximation.GGT.RelHypOsinTheorem24Refuted

/-!
# Osin's Theorem 2.4 at the relative Cayley graph: the fourth generation

Three generations of the weighted leaf have been refuted, and the diagnosis of
`GGT/RelHypOsin24Collapse.lean` is that the defect was never the length floor,
the notion of piece, or the quantifier order: it was that the length function
was an abstract `RelativeLength` -- five clauses, no geometry -- where Osin's
Theorem 2.4 is stated for the relative Cayley graph `Γ(G, X ⊔ ℋ)` of a
**finite** relative generating set `X` over a pair `(G, {H_λ})` that is
genuinely relatively hyperbolic.

This module states the theorem at that object.  The length function is not a
parameter any more: it is `RelativeGeneratingSet.relLength`, the word metric of
the alphabet `X ⊔ ℋ`, and `relLengthOf` packages it as the `RelativeLength` the
letter calculus consumes.  Two hypotheses of the earlier generations disappear
as a result, because they are now theorems:

* `HasGeodesicSpellings` -- a word metric attains its infimum
  (`hasGeodesicSpellings_relLengthOf`);
* the letters clause `L.len a ≤ 1` and membership in the alphabet are the same
  condition (`mem_alphabet_iff_relLength_le_one`) -- the unit ball of the
  relative metric **is** `X ⊔ ℋ`, which is the fact every refutation so far has
  turned on.

## Why each earlier witness fails a hypothesis of this generation

* **The collapse witness** (`GGT/RelHypOsin24Collapse.lean`: `ℤ * ℤ`, length
  `max (indicator) (norm of the abelianisation)`, relators `t^{±m}`).  It fails
  at the alphabet.  Its unit ball contains every commutator of the two factors,
  in particular the infinitely many pairwise distinct elements `[t^m, s]`, so it
  is not the unit ball of `X ⊔ ℋ` for any finite `X`:
  `RelHypOsin24CayleyWitness.not_isRelLength_collapse` proves exactly that, from
  `mem_alphabet_of_relLength_le_one` and finiteness of `X.carrier`.  Note that
  the relator family itself survives -- at the honest metric the family
  `{t^m, t^{-m}}` still satisfies every hypothesis, and its Greendlinger
  conclusion is then true rather than false, since `[t^m, s]` costs `2m + 2`
  letters instead of one.
* **osin24's witness** (`GGT/RelHypOsinTheorem24Refuted.lean`: the alphabet
  `{1, t^{±1}, t^{±42}}`, relator `t` repeated `42` times).  Its length function
  *is* the word metric of a finite alphabet, so it passes the clause the
  collapse witness fails.  It fails the geodesicity clause instead, and that is
  already a theorem: `not_geodesic_w`.  A `42`-letter word spelling an element
  of relative length one is not a geodesic word.
* **The abelian-partner design** (`GGT/RelHypAbelianPartnerNoGo.lean`).  This
  one is not excluded by any clause of the leaf, and it is not expected to be:
  the no-go is conditional on a `WeightedRouterDesign` existing whose relators
  meet the geodesicity and group-piece certificates **over a finite `X`**, and
  the reason to expect none is on the design side.  With `X` finite and the
  partner abelian, a tie relator is a source letter followed by a geodesic word
  of the partner, and over an abelian group such words are periodic: the
  rotations of one relator then share a prefix of length `|r| - O(1)`, which
  `LetterMetricGroupSmallCancellation` at `1/7` forbids.  That is the argument
  the third generation's docstring wanted and could not have, because it needs
  the alphabet to be fixed and finite.  It is stated here as the reason the
  obstruction is not expected to fire, not as a theorem of this module.

## What is still a transcription and not a theorem

`OsinTheorem24Cayley` below is an unproved `Prop`.  It replaces a **refuted**
one, and `GGT/RelHypOsin24CayleyEndpoint.lean` re-derives the Fournier-Facio
quotient sentence from it, so the chain no longer rests on a false hypothesis;
but the Greendlinger content itself is not proved here.

## CORRECTION (issue #52): this generation is unfaithful in four places, and is
retired from hypothesis position

An earlier version of this paragraph claimed that Osin's piece "is
`LetterIsGroupPiece` on the nose", so that
`LetterMetricGroupSmallCancellation` is his `C'(λ)` and not a weakening of it.
**That is false.**  Read against the source -- Osin, *Small cancellations over
relatively hyperbolic groups and embedding theorems*, Ann. of Math. **172**
(2010) 1--39, arXiv:math/0411039 -- four clauses are wrong:

* **Definition 4.1, the ε-fudge, is missing.**  A subword `U` of `R` is an
  **ε-piece** if `R ≡ UV`, `R' ≡ U'V'`, and `U' = Y U Z` in `G` for words with
  `max{‖Y‖, ‖Z‖} ≤ ε`.  `LetterIsGroupPiece` is the `Y = Z = 1` case, so it
  recognises fewer pieces, so the metric condition is a **weaker** hypothesis
  and this leaf claims strictly **more** than Osin proves.  And `ε` is not a
  free parameter to set to zero: Lemma 4.4 *produces* it from `(λ, c, µ)`.
* **Definition 4.1(3), the rotation exemption, is missing.**  Osin's third
  clause `Y R Y⁻¹ ≠ R'` exempts exactly the overlaps of a relator with its own
  cyclic shifts, which for a symmetrized family are `Y R Y⁻¹`.
  `LetterIsGroupPiece` exempts only `r₁ ≠ r₂` as *lists*, so it counts them.
  That makes the *design* obligation strictly stronger than Osin's, in the
  opposite direction to the first defect.
* **The small-cancellation constant has the wrong quantifier and the wrong
  range.**  Lemma 5.1 reads `∀ λ, c, N. ∃ µ, ε, ρ. ∀ R satisfying
  C(ε, µ, λ, c, ρ)`, and Lemma 4.4 restricts `µ ∈ (0, 1/16]`.  Osin's `λ` is
  the *quasi-geodesic* constant; his `µ` is the small-cancellation constant,
  and it is the `lam` of this file.  Here `lam` is **universally** quantified
  and consumed at `1/7`, against designs certified at `C'(1/8)`; both exceed
  `1/16`, so the leaf is spent outside the range in which Osin proves it, and
  `ε` does not appear at all.
* **The torsion half needs `C₁`, not `C`.**  Osin's finite-order statement
  carries the `C₁(ε, µ, λ, c, ρ)`-condition, which asks the piece bound also for
  **ε′-pieces** -- the self-overlaps `R ≡ U V U' V'` with `U' = Y U^{±1} Z`.
  `WeightedTorsionLeafCayley` substitutes `LetterNoProperPower`, which is a
  different hypothesis.

One suspicion is **refuted** and is worth recording as such: there is no
isolated-components clause to add.  Definition 4.2 has exactly three clauses --
`‖R‖ ≥ ρ`, `(λ, c)`-quasi-geodesic, and the ε-piece bound.  Isolated components
and contiguity subdiagrams are proof machinery in Lemma 4.4 and §5--§7, not
hypotheses on `R`.

The geodesicity observation of the old paragraph stands: Osin states the
conclusion about *words* and this repository states it about the *element* they
spell (`RelativeLengthBound`), and the two agree only on geodesic relators.

**None of this is repaired by a fifth generation**, because the machinery was
never the citation.  Osin's Theorem 2.4 has no small-cancellation hypothesis at
all, and the statement Fournier-Facio actually cites is
`GGT/RelHypFournierFacioProp23.FournierFacioProposition23`.  `OsinTheorem24Cayley`
and `OsinRelatorDesignCayley` are retired from hypothesis position and kept as
the record of what was checked.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.OsinWeightedMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## 1.  The unit ball of the relative metric is the alphabet -/

/-- **A nonidentity element of relative length at most one is a letter.**

The word norm attains its infimum, so an element of length one is spelled by a
one-letter word, and that letter is the element.  This is the fact the three
refutations turn on, in the direction that makes the fourth generation immune:
fixing a *finite* `X` bounds the unit ball by `X` together with the peripheral
subgroups, and no length function whose unit ball is larger can arise from a
relative generating set. -/
theorem mem_alphabet_of_relLength_le_one {G : Type u} [Group G] {ι : Type v}
    {H : ι → Subgroup G} (X : RelativeGeneratingSet G H) {g : G} (hg : g ≠ 1)
    (h : X.relLength g ≤ 1) : g ∈ X.alphabet.carrier := by
  obtain ⟨l, hl, hlen⟩ :=
    WordMetric.exists_isWord_length_eq X.alphabet.symmetricGenerating g
  have hl1 : l.length ≤ 1 := by rw [hlen]; exact h
  rcases l with _ | ⟨a, t⟩
  · exact absurd (by simpa using hl.prod_eq.symm) hg
  · rcases t with _ | ⟨b, t'⟩
    · have hag : a = g := by simpa using hl.prod_eq
      rw [← hag]
      exact hl.letters a (by simp)
    · simp only [List.length_cons] at hl1
      omega

/-- **A letter has relative length at most one**, the converse direction. -/
theorem relLength_le_one_of_mem_alphabet {G : Type u} [Group G] {ι : Type v}
    {H : ι → Subgroup G} (X : RelativeGeneratingSet G H) {g : G}
    (hg : g ∈ X.alphabet.carrier) : X.relLength g ≤ 1 :=
  WordMetric.wordNorm_le_one_of_mem hg

/-- **The unit ball of `Γ(G, X ⊔ ℋ)` is the alphabet.**  Stated with an explicit
peripheral index because the identity is a letter only through the peripheral
subgroups, which is where it lives. -/
theorem mem_alphabet_iff_relLength_le_one {G : Type u} [Group G] {ι : Type v}
    {H : ι → Subgroup G} (X : RelativeGeneratingSet G H) (l : ι) (g : G) :
    g ∈ X.alphabet.carrier ↔ X.relLength g ≤ 1 := by
  refine ⟨relLength_le_one_of_mem_alphabet X, fun h => ?_⟩
  rcases eq_or_ne g 1 with rfl | hg
  · exact X.peripheral_subset_alphabet l (one_mem _)
  · exact mem_alphabet_of_relLength_le_one X hg h

/-! ## 2.  The peripheral factor of a free product, and the metric it carries -/

/-- **The peripheral subgroup of a two-factor free product**: the image of the
source factor.  `freeProductPeripheral` is this at `pairFamily U H`; the general
form is needed because the leaf below quantifies over the family. -/
def sourceFactor (G : Bool → Type) [∀ b, Group (G b)] : Subgroup (CoprodI G) :=
  MonoidHom.range (CoprodI.of : G false →* CoprodI G)

theorem sourceFactor_pairFamily (U H : Type) [Group U] [Group H] :
    sourceFactor (pairFamily U H) = freeProductPeripheral U H := rfl

theorem of_mem_sourceFactor {G : Bool → Type} [∀ b, Group (G b)] (x : G false) :
    (CoprodI.of x : CoprodI G) ∈ sourceFactor G :=
  ⟨x, rfl⟩

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- **The relative metric of `X ⊔ ℋ`, as the letter calculus consumes it.**

Not a new length function: `RelativeLength.len` is `RelativeGeneratingSet.
relLength` on the nose (`relLengthOf_len`).  The peripheral clause
`len_source_le_one` is Osin's own -- a peripheral element is one letter -- and
here it is a theorem rather than an axiom, because the alphabet contains the
peripheral subgroup. -/
noncomputable def relLengthOf
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G)) :
    RelativeLength G :=
  ofSymmetricGeneratingSet X.alphabet.symmetricGenerating
    fun x => X.peripheral_subset_alphabet () (of_mem_sourceFactor x)

theorem relLengthOf_len
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G)) :
    (relLengthOf X).len = X.relLength := rfl

/-- **Geodesic spellings are free at the real object.**  The word metric attains
its infimum, so the hypothesis every earlier generation carried is a theorem
here. -/
theorem hasGeodesicSpellings_relLengthOf
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G)) :
    HasGeodesicSpellings (relLengthOf X) :=
  hasGeodesicSpellings_ofSymmetricGeneratingSet _ _

/-- The letters clause of the earlier generations and membership in `X ⊔ ℋ` are
the same condition. -/
theorem mem_alphabet_of_relLengthOf_le_one
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G))
    {a : CoprodI G} (h : (relLengthOf X).len a ≤ 1) : a ∈ X.alphabet.carrier :=
  (mem_alphabet_iff_relLength_le_one X () a).mpr h

theorem relLengthOf_le_one_of_mem_alphabet
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G))
    {a : CoprodI G} (h : a ∈ X.alphabet.carrier) : (relLengthOf X).len a ≤ 1 :=
  relLength_le_one_of_mem_alphabet X h

/-! ## 3.  The fourth-generation leaves -/

/-- **Osin, Theorem 2.4(1), at the relative Cayley graph.**

Relators are words in `X ⊔ ℋ`, cyclically reduced, geodesic, longer than the
floor `ρ`; pieces are Osin's, compared in the group; and the conclusion is the
relative Greendlinger bound at the relative metric.  Compare the three refuted
forms: what has changed is that `L` is no longer a parameter but the word metric
of a finite relative generating set, and `HasGeodesicSpellings` has left the
hypothesis list because it is now provable. -/
def WeightedGreendlingerLeafCayley
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G))
    (R : Set (List (CoprodI G))) (rho : ℕ) (lam : ℚ) : Prop :=
  LetterSymmetrized R →
    (∀ r ∈ R, LetterReduced (relLengthOf X) r) →
      (∀ r ∈ R, ∀ a ∈ r, a ∈ X.alphabet.carrier) →
        (∀ r ∈ R, LetterGeodesic (relLengthOf X) r) →
          (∀ r ∈ R, rho ≤ r.length) →
            LetterFragmentSlack R lam →
              LetterMetricGroupSmallCancellation R lam →
                RelativeLengthBound (relLengthOf X) R

/-- **Osin, Theorem 2.4(5), at the relative Cayley graph.** -/
def WeightedTorsionLeafCayley
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G))
    (R : Set (List (CoprodI G))) (rho : ℕ) (lam : ℚ) : Prop :=
  LetterSymmetrized R →
    (∀ r ∈ R, LetterReduced (relLengthOf X) r) →
      (∀ r ∈ R, ∀ a ∈ r, a ∈ X.alphabet.carrier) →
        (∀ r ∈ R, LetterGeodesic (relLengthOf X) r) →
          (∀ r ∈ R, rho ≤ r.length) →
            LetterFragmentSlack R lam →
              LetterMetricGroupSmallCancellation R lam →
                LetterNoProperPower R →
                  TorsionLifts (letterRelatorSubgroup R)

/-! ## 4.  The relatively hyperbolic hypothesis, and the universal closure -/

/-- **`(G, {U})` is relatively hyperbolic, certified at this very `X`.**  Both
clauses of `IsRelativelyHyperbolic` at the generating set the metric uses, which
is what Osin's theorem needs: `IsRelativelyHyperbolic` produces *some* relative
generating set, and transporting hyperbolicity from that one to another is
Osin's independence theorem, which this repository does not have. -/
def IsRelHypAt
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G)) :
    Prop :=
  ∃ delta : ℝ, HullGeometry.IsHyperbolicSpace delta (Cayley X.alphabet) ∧
    PeripheralMetricLocallyFinite X

/-- **The hypothesis is the repo's `IsRelativelyHyperbolic`, unbundled.**  So the
leaf below claims nothing about pairs that are not relatively hyperbolic, and a
consumer holding `IsRelativelyHyperbolic` has an `X` to feed it. -/
theorem isRelativelyHyperbolic_iff_exists_relHypAt :
    IsRelativelyHyperbolic (CoprodI G) (fun _ : Unit => sourceFactor G) ↔
      ∃ X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G),
        IsRelHypAt X := by
  constructor
  · rintro ⟨X, delta, h1, h2⟩
    exact ⟨X, delta, h1, h2⟩
  · rintro ⟨X, delta, h1, h2⟩
    exact ⟨X, delta, h1, h2⟩

theorem isRelativelyHyperbolic_of_relHypAt
    {X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G)}
    (h : IsRelHypAt X) :
    IsRelativelyHyperbolic (CoprodI G) (fun _ : Unit => sourceFactor G) :=
  isRelativelyHyperbolic_iff_exists_relHypAt.mpr ⟨X, h⟩

/-- **Osin, "Small cancellations over relatively hyperbolic groups", Theorem 2.4,
clauses (1) and (5), at the relative Cayley graph.**

The binder order is the theorem's: the pair `(G, {U})`, the finite relative
generating set `X`, and its hyperbolicity come first; `ρ` is produced from them
and from `λ`; and only then is the symmetrized relator family quantified.

Compare `OsinTheorem24`, `OsinTheorem24Repaired` (both refuted by
`GGT/RelHypOsin24Collapse.lean`) and the third generation: there the length
function was an arbitrary `RelativeLength`, five clauses with no geometry, and
that is what every refutation exploited. -/
def OsinTheorem24Cayley : Prop :=
  ∀ (G : Bool → Type) (_ : ∀ b, Group (G b))
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G)),
    IsRelHypAt X → ∀ lam : ℚ, ∃ rho : ℕ, ∀ R : Set (List (CoprodI G)),
      WeightedGreendlingerLeafCayley X R rho lam ∧
        WeightedTorsionLeafCayley X R rho lam

/-! ## 5.  The model test at the smallest family -/

/-- **The empty family satisfies the Greendlinger leaf.**  The new clauses have
not made it unsatisfiable. -/
theorem weightedGreendlingerLeafCayley_empty
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G))
    (rho : ℕ) (lam : ℚ) :
    WeightedGreendlingerLeafCayley X (∅ : Set (List (CoprodI G))) rho lam :=
  fun _ _ _ _ _ _ _ =>
    relativeLengthBound_of_eq_bot letterRelatorSubgroup_empty

/-- **The empty family satisfies the torsion leaf.** -/
theorem weightedTorsionLeafCayley_empty
    (X : RelativeGeneratingSet (CoprodI G) (fun _ : Unit => sourceFactor G))
    (rho : ℕ) (lam : ℚ) :
    WeightedTorsionLeafCayley X (∅ : Set (List (CoprodI G))) rho lam :=
  fun _ _ _ _ _ _ _ _ => torsionLifts_of_eq_bot letterRelatorSubgroup_empty

end RelHyp
end GGT
end GroupApproximation
