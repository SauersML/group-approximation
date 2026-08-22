import GroupApproximation.Sofic.RelativeRouterEnvelope
import GroupApproximation.Algebra.WordMetric

/-!
# The weighted relative metric: Osin's alphabet `X ∪ U`, and the Kazhdan
envelope it makes possible

`Sofic.RelativeRouterEnvelope` runs the router relatively over `U * B` and
proves that the route **cannot** reach property `(T)`: making the partner's
image fill the quotient forces a relation `u = y` with `u` in the source factor
and `y` in the partner factor, that relation is a member of the relator subgroup
of *syllable* length at most two, and the fragment slack forces every relator to
have at least `42` syllables.  The tie is refuted by arithmetic.

The refutation is an artifact of the metric, not of the construction.  In
`OsinSmallCancellation.wlen` a syllable costs one, so an element of the partner
factor — however long its own word is — costs one.  Osin's relative small
cancellation measures lengths in the alphabet `X ∪ U`, where `X` is a finite
generating set of the non-peripheral factor and `U` is the peripheral subgroup:
a peripheral element is one letter, a partner element costs its `X`-word length.
In that metric the tie relator `u · w⁻¹` is as long as `w`, and the floor is met.

**This module is that metric, and the whole lane re-run over it.**

## The one axiom that does the work

A relative length function (`RelativeLength`) is a length function on `U * B` —
zero only at the identity, subadditive, inversion-invariant — with one extra
clause:

    len_source_le_one : ∀ x : G false, len (CoprodI.of x) ≤ 1

*Every element of the source factor is a single letter.*  That is what
`peripheral = {U}` means, and it is the entire content of the refinement,
because it is asymmetric: nothing is assumed about the partner factor, whose
elements may be arbitrarily long.  The asymmetry propagates exactly where it is
needed —

* `factorMap_source_injective` — **`U` still embeds**, proved outright, no leaf:
  a difference of two source elements is one letter, the length bound would
  demand a relator shorter than two, and the floor is `42`;
* the same argument at the partner index **fails, and must fail**: a partner
  element is not a letter, so nothing bounds `len (of y)`, and
  `RelativeRouterEnvelope.exists_injective_to_partner` shows that if it did not
  fail then `U` would embed in `B`.

So the weighted metric breaks the symmetry between the two factors that killed
the unweighted design, and it breaks it in the one direction the envelope needs.

## The old lane is the degenerate case

`syllableLength` is a `RelativeLength` — the five laws are
`FreeProductCyclic.sylLength_eq_zero_iff`, `sylLength_mul_le`, `sylLength_inv`
and `sylLength_of_le_one`.  At that model `sylLength_of_le_one` applies to the
*partner* index too (`syllableLength_partner_le_one`), every tie is short, and
`not_relativeLengthBound_of_light_tie` reproduces
`RelativeRouterEnvelope.not_partnerSurjective`.  The previous refutation is
therefore this file's theorem at one particular length function, and the lane it
refuted is the lane in which the partner is atomic.

## Torsion, restated so the partner may collapse

The unweighted layer derives torsion-freeness from `TorsionIntoFactors` together
with injectivity of `factorMap` **at every index** — including the partner, which
the weighted lane must not have.  `TorsionLifts` replaces it with Osin's own
form: every finite-order element of the quotient lifts to a finite-order element
upstairs.  Then `isPowerTorsionFree_of_torsionLifts` needs nothing but ambient
torsion-freeness, which is `isPowerTorsionFree_coprodI` from the two factors, and
`torsionLifts_of_torsionIntoFactors` records that the new form is no stronger
than the old one wherever the old one applies.

## What is open

Two leaves, the weighted twins of `GreendlingerRelativeTransfer`'s, stated at
the letter alphabet and at the same concrete pair `(1/7, 42)`:

* `WeightedGreendlingerLeaf` — symmetrized, cyclically reduced, letters of
  length at most one, fragment slack, `C'(1/7)`  ⟹  `RelativeLengthBound`;
* `WeightedTorsionLeaf` — the same, plus no proper powers  ⟹  `TorsionLifts`.

Both hold outright for the empty family.  Nothing else in this file is
conditional: `factorMap_source_injective`, `partnerHom_surjective`, `kazhdan`,
`finitelyPresented`, `isPowerTorsionFree_coprodI` and the whole of section 8 are
theorems.  **In particular `kazhdanEnvelope_of_design` no longer carries a
property-`(T)` hypothesis** — that clause is now derived, from the tie, which is
what the weighted metric legalizes.

Names are kept disjoint from `Sofic.GreendlingerRelativeTransfer` (owned by the
relative-transfer lane): every letter-level predicate here carries the `Letter`
prefix, and the length-level ones are `RelativeLength*`.

The fragment slack keeps the same shape and the same numbers as the unweighted
lane, `lam · |r| + 1 ≤ (1/6) · |r|` at `lam = 1/7` and `|r| ≥ 42`, because the
alphabet is atomic: the one-letter correction now accounts for a path entering
and leaving a peripheral coset rather than for a fragment of a syllable.  What
changed is not the inequality but what `|r|` counts — letters, not syllables — and
that is exactly why a tie relator can meet the floor.
-/

namespace GroupApproximation
namespace OsinWeightedMetric

open Monoid Monoid.CoprodI OsinSmallCancellation
open FournierFacioUniversal

/-! ## 0.  The ambient free product is torsion-free -/

section Ambient

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- **A free product of torsion-free groups is torsion-free.**  The classification
`FreeProductCyclic.torsion_conj_into_factor` already carries the factor element's
own relation `x ^ n = 1`, so torsion-freeness of the factor finishes in one
rewrite.

This replaces the route through `isPowerTorsionFree_of_torsionIntoFactors`, which
needs the factors to stay embedded in a quotient; here there is no quotient. -/
theorem isPowerTorsionFree_coprodI (hfree : ∀ i, IsPowerTorsionFree (G i)) :
    IsPowerTorsionFree (CoprodI G) := by
  intro g n hn hg
  rcases FreeProductCyclic.torsion_conj_into_factor hn hg with h | ⟨i, x, c, hxn, rfl⟩
  · exact h
  · rw [hfree i x n hn hxn]
    simp

/-- A relation of the shape `a · c⁻¹` identifies `a` with `c` in the quotient.
The only way a tie is ever used. -/
theorem mk_eq_mk_of_mem {K : Subgroup (CoprodI G)} [K.Normal] {a c : CoprodI G}
    (h : a * c⁻¹ ∈ K) :
    QuotientGroup.mk' K a = QuotientGroup.mk' K c := by
  have h1 : QuotientGroup.mk' K (a * c⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

end Ambient

/-! ## 1.  The relative length function

Osin's relative metric, axiomatized.  The first four clauses say `len` is a
length function; the fifth is the peripheral clause, and it is the only place
the two factors are treated differently. -/

/-- **A relative length function on `U * B`.**

The intended model is the word metric of the alphabet `X ∪ U` — every element of
the source factor is one letter, every partner element is spelled in a finite
generating set `X` of the partner — and `ofSymmetricGeneratingSet` in section 9
builds exactly that.  Everything in this file is proved from the five clauses
alone, so any other model does as well. -/
structure RelativeLength (G : Bool → Type) [∀ b, Group (G b)] where
  /-- The length of an element of the free product. -/
  len : CoprodI G → ℕ
  /-- The identity is empty. -/
  len_one : len 1 = 0
  /-- Only the identity is empty. -/
  eq_one_of_len_eq_zero : ∀ g, len g = 0 → g = 1
  /-- Concatenation. -/
  len_mul_le : ∀ g h, len (g * h) ≤ len g + len h
  /-- Reading a word backwards. -/
  len_inv : ∀ g, len g⁻¹ = len g
  /-- **The peripheral clause.**  Every element of the source factor is a single
  letter.  Nothing is assumed about the partner factor: that asymmetry is the
  whole refinement. -/
  len_source_le_one : ∀ x : G false, len (CoprodI.of x) ≤ 1

namespace RelativeLength

variable {G : Bool → Type} [∀ b, Group (G b)] (L : RelativeLength G)

/-- A nonidentity element has positive length. -/
theorem one_le_len {g : CoprodI G} (hg : g ≠ 1) : 1 ≤ L.len g := by
  rcases Nat.eq_zero_or_pos (L.len g) with h | h
  · exact absurd (L.eq_one_of_len_eq_zero g h) hg
  · exact h

/-- **A word of letters is no longer than its letter count.**  The consistency
statement between the length function and the letter alphabet: a relator spelled
by `n` letters names an element of length at most `n`. -/
theorem len_prod_le {l : List (CoprodI G)} (h : ∀ a ∈ l, L.len a ≤ 1) :
    L.len l.prod ≤ l.length := by
  induction l with
  | nil => simp [L.len_one]
  | cons a t ih =>
      have ha : L.len a ≤ 1 := h a (by simp)
      have ht : L.len t.prod ≤ t.length := ih fun b hb => h b (by simp [hb])
      have hm := L.len_mul_le a t.prod
      rw [List.prod_cons, List.length_cons]
      omega

end RelativeLength

/-! ### The degenerate model: syllable length

Every clause is an existing theorem.  The point of recording it is section 8:
at this model the *partner* factor is atomic too, and the previous lane's
refutation is exactly what follows. -/

section SyllableModel

variable (G : Bool → Type) [∀ b, Group (G b)] [∀ b, DecidableEq (G b)]

/-- **Syllable length is a relative length function.**  So `RelativeLength` is
inhabited, and the unweighted lane is one of its models. -/
noncomputable def syllableLength : RelativeLength G where
  len := FreeProductCyclic.sylLength
  len_one := FreeProductCyclic.sylLength_eq_zero_iff.mpr rfl
  eq_one_of_len_eq_zero := fun _ h => FreeProductCyclic.sylLength_eq_zero_iff.mp h
  len_mul_le := FreeProductCyclic.sylLength_mul_le
  len_inv := FreeProductCyclic.sylLength_inv
  len_source_le_one := fun x => FreeProductCyclic.sylLength_of_le_one x

/-- The model's length is syllable length on the nose, so a statement at this
model is a statement about `OsinSmallCancellation`'s metric with no transport. -/
theorem syllableLength_len :
    (syllableLength G).len = FreeProductCyclic.sylLength := rfl

/-- **The degeneracy, named.**  At the syllable model the partner factor is
atomic as well: every one of its elements is a single letter.  That is the
hypothesis `not_relativeLengthBound_of_light_tie` consumes, and it is why the
unweighted lane collapses. -/
theorem syllableLength_partner_le_one (y : G true) :
    (syllableLength G).len (CoprodI.of y) ≤ 1 :=
  FreeProductCyclic.sylLength_of_le_one y

end SyllableModel

/-! ## 2.  The letter-level relator calculus

Relators are lists of *letters* — elements of the free product, each of length at
most one — so lengths are `List.length` and pieces are prefixes, with no
syllable granularity anywhere.  This mirrors
`Sofic.OsinRelativeSmallCancellation` clause for clause, with `wlen` replaced by
`List.length` and `Word G` by `List (CoprodI G)`. -/

section Letters

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- The normal subgroup a letter-level relator family presents. -/
def letterRelatorSubgroup (R : Set (List (CoprodI G))) : Subgroup (CoprodI G) :=
  Subgroup.normalClosure (List.prod '' R)

/-- Registered for the same reason as `OsinSmallCancellation.relatorSubgroup_normal`:
instance search stops at the `def`, and the quotient needs a group. -/
instance letterRelatorSubgroup_normal (R : Set (List (CoprodI G))) :
    (letterRelatorSubgroup R).Normal :=
  Subgroup.normalClosure_normal

theorem mem_letterRelatorSubgroup {R : Set (List (CoprodI G))}
    {r : List (CoprodI G)} (hr : r ∈ R) : r.prod ∈ letterRelatorSubgroup R :=
  Subgroup.subset_normalClosure ⟨r, hr, rfl⟩

/-- **A piece**: a common initial segment of two distinct relators of the
symmetrized family. -/
def LetterIsPiece (R : Set (List (CoprodI G))) (p : List (CoprodI G)) : Prop :=
  ∃ r₁ ∈ R, ∃ r₂ ∈ R, r₁ ≠ r₂ ∧ p <+: r₁ ∧ p <+: r₂

/-- **The metric condition `C'(lam)`**, letters counted. -/
def LetterMetricSmallCancellation (R : Set (List (CoprodI G))) (lam : ℚ) : Prop :=
  ∀ p, LetterIsPiece R p → ∀ r ∈ R, p <+: r →
    (p.length : ℚ) < lam * (r.length : ℚ)

/-- **The family is symmetrized**: closed under cyclic rotation and under formal
inversion. -/
def LetterSymmetrized (R : Set (List (CoprodI G))) : Prop :=
  (∀ r ∈ R, ∀ n : ℕ, r.rotate n ∈ R) ∧
    (∀ r ∈ R, ((r.map fun a => a⁻¹).reverse) ∈ R)

/-- **No relator is a proper power.**  Without it the quotient acquires torsion
of its own; the `(xy)^7` witness of `GreendlingerRelativeTransfer` is unaffected
by the change of alphabet. -/
def LetterNoProperPower (R : Set (List (CoprodI G))) : Prop :=
  ∀ r ∈ R, ∀ (s : CoprodI G) (k : ℕ), 2 ≤ k → r.prod ≠ s ^ k

/-- **Cyclically reduced**: no two cyclically adjacent letters cancel.  The
rotation quantifier is what makes it cyclic. -/
def LetterCyclicallyReduced (r : List (CoprodI G)) : Prop :=
  ∀ (n : ℕ) (a b : CoprodI G) (t : List (CoprodI G)),
    r.rotate n = a :: b :: t → a * b ≠ 1

/-- **The Greendlinger length bound, at the relative length.**  A nontrivial
element of the relator subgroup is longer — *in the relative metric* — than half
of some relator's letter count.

This is the one place the length function and the letter alphabet meet, and the
asymmetry lives here: for a source element the left side is at most one, for a
partner element it is unbounded. -/
def RelativeLengthBound (L : RelativeLength G) (R : Set (List (CoprodI G))) :
    Prop :=
  ∀ g : CoprodI G, g ≠ 1 → g ∈ letterRelatorSubgroup R →
    ∃ r ∈ R, r.length < 2 * L.len g

/-- **The fragment slack**, same inequality and same numbers as the unweighted
lane; only `|r|` has changed meaning, from syllables to letters. -/
def LetterFragmentSlack (R : Set (List (CoprodI G))) (lam : ℚ) : Prop :=
  ∀ r ∈ R, lam * (r.length : ℚ) + 1 ≤ (1 / 6) * (r.length : ℚ)

/-- The concrete pair, `lam ≤ 1/7` against relators of at least `42` letters,
since `1/6 - 1/7 = 1/42`.  The only place the two numbers appear. -/
theorem letterFragmentSlack_of_le_seventh {R : Set (List (CoprodI G))} {lam : ℚ}
    (hlam : lam ≤ 1 / 7) (hlong : ∀ r ∈ R, 42 ≤ r.length) :
    LetterFragmentSlack R lam := by
  intro r hr
  have hw : (42 : ℚ) ≤ (r.length : ℚ) := by exact_mod_cast hlong r hr
  have h1 : lam * (r.length : ℚ) ≤ (1 / 7) * (r.length : ℚ) :=
    mul_le_mul_of_nonneg_right hlam (by linarith)
  linarith

/-! ### The degenerate family -/

theorem letterRelatorSubgroup_empty :
    letterRelatorSubgroup (∅ : Set (List (CoprodI G))) = ⊥ := by
  refine le_antisymm ?_ bot_le
  apply Subgroup.normalClosure_le_normal
  simp

theorem relativeLengthBound_of_eq_bot {L : RelativeLength G}
    {R : Set (List (CoprodI G))} (hR : letterRelatorSubgroup R = ⊥) :
    RelativeLengthBound L R := by
  intro g hg hmem
  rw [hR, Subgroup.mem_bot] at hmem
  exact absurd hmem hg

end Letters

/-! ## 3.  Torsion, in the form the weighted lane needs

The unweighted layer spends injectivity of `factorMap` at *every* index.  The
weighted lane must not have it at the partner index — that is the whole point —
so the torsion clause is restated in Osin's own form, which mentions no factor
map at all. -/

section Torsion

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- **Osin's torsion clause.**  Every element of finite order in the quotient is
the image of an element of finite order upstairs. -/
def TorsionLifts (K : Subgroup (CoprodI G)) [K.Normal] : Prop :=
  ∀ (q : CoprodI G ⧸ K) (n : ℕ), 0 < n → q ^ n = 1 →
    ∃ g : CoprodI G, QuotientGroup.mk' K g = q ∧ ∃ m : ℕ, 0 < m ∧ g ^ m = 1

/-- **The torsion clause, spent.**  A quotient of a torsion-free group in which
torsion lifts is torsion-free.  No factor map, no embedding clause. -/
theorem isPowerTorsionFree_of_torsionLifts {K : Subgroup (CoprodI G)} [K.Normal]
    (hamb : IsPowerTorsionFree (CoprodI G)) (h : TorsionLifts K) :
    IsPowerTorsionFree (CoprodI G ⧸ K) := by
  intro q n hn hq
  obtain ⟨g, hgq, m, hm, hgm⟩ := h q n hn hq
  rw [← hgq, hamb g m hm hgm, map_one]

/-- **The new form is no stronger than the old one.**  Where the unweighted
classification applies — torsion conjugating into the factors, with every factor
embedded — it delivers `TorsionLifts`.  So restating the clause costs nothing and
buys freedom at the partner index. -/
theorem torsionLifts_of_torsionIntoFactors {K : Subgroup (CoprodI G)} [K.Normal]
    (htor : TorsionIntoFactors K)
    (hinj : ∀ i, Function.Injective (factorMap K i)) : TorsionLifts K := by
  intro q n hn hq
  rcases htor q n hn hq with h | ⟨i, x, c, rfl⟩
  · exact ⟨1, by rw [map_one, h], 1, Nat.one_pos, one_pow 1⟩
  · obtain ⟨c₀, rfl⟩ := QuotientGroup.mk'_surjective K c
    have h3 : QuotientGroup.mk' K c₀ * (factorMap K i x) ^ n
        * (QuotientGroup.mk' K c₀)⁻¹ = 1 := by
      rw [← FreeProductCyclic.conj_pow_eq]
      exact hq
    have h2 : (factorMap K i x) ^ n = 1 :=
      FreeProductCyclic.eq_one_of_conj_eq_one h3
    have h5 : x ^ n = 1 := by
      apply hinj i
      rw [map_pow, h2, map_one]
    refine ⟨c₀ * CoprodI.of x * c₀⁻¹, ?_, n, hn, ?_⟩
    · rw [map_mul, map_inv, map_mul]
    · rw [FreeProductCyclic.conj_pow_eq, ← map_pow, h5, map_one, mul_one,
        mul_inv_cancel]

/-- The degenerate family: with no relators the quotient map only renames, so
torsion lifts outright. -/
theorem torsionLifts_of_eq_bot {K : Subgroup (CoprodI G)} [K.Normal]
    (hK : K = ⊥) : TorsionLifts K := by
  intro q n hn hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K q
  refine ⟨g, rfl, n, hn, ?_⟩
  have h2 : QuotientGroup.mk' K (g ^ n) = 1 := by rw [map_pow]; exact hq
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', hK, Subgroup.mem_bot] at h2
  exact h2

end Torsion

/-! ## 4.  The two leaves, at the weighted metric

The weighted twins of `GreendlingerRelativeTransfer.RelativeGreendlingerLeaf`
and `GreendlingerRelativeTransfer.RelativeTorsionLeaf`, renamed so that a module
opening both namespaces sees no ambiguity — the relative-transfer lane owns the
`Relative*Leaf` names and this lane owns the `Weighted*Leaf` ones.

Neither reduces to its unweighted counterpart: the
metric condition constrains letter-pieces and the unweighted one constrains
syllable-pieces, and neither family of pieces contains the other.  What the
weighted forms buy is that their *conclusions* are the ones the weighted lane
consumes, and that the Greendlinger conclusion is now a demand about a genuinely
atomic alphabet, with no fragment ambiguity inside a letter. -/

section Leaves

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- **OPEN LEAF.**  The relative Greendlinger lemma at the letter alphabet.

The proof to write is Lyndon--Schupp Ch. V §§9--11 over `X ∪ U`: a reduced van
Kampen diagram over `U * B` whose boundary reads the relative normal form, the
curvature count on its interior, and the boundary-layer estimate that `C'(1/6)`
turns into "more than half".  `LetterFragmentSlack` licenses the step to the
classical constant. -/
def WeightedGreendlingerLeaf (L : RelativeLength G)
    (R : Set (List (CoprodI G))) (lam : ℚ) : Prop :=
  LetterSymmetrized R → (∀ r ∈ R, LetterCyclicallyReduced r) →
    (∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1) →
    LetterFragmentSlack R lam → LetterMetricSmallCancellation R lam →
    RelativeLengthBound L R

/-- **OPEN LEAF.**  The relative torsion classification at the letter alphabet,
stated at `TorsionLifts` — the form that mentions no factor map, so that the
partner factor is free to collapse. -/
def WeightedTorsionLeaf (L : RelativeLength G)
    (R : Set (List (CoprodI G))) (lam : ℚ) : Prop :=
  LetterSymmetrized R → (∀ r ∈ R, LetterCyclicallyReduced r) →
    (∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1) →
    LetterFragmentSlack R lam → LetterMetricSmallCancellation R lam →
    LetterNoProperPower R → TorsionLifts (letterRelatorSubgroup R)

/-- **Neither leaf is empty.** -/
theorem weightedGreendlingerLeaf_empty {L : RelativeLength G} {lam : ℚ} :
    WeightedGreendlingerLeaf L (∅ : Set (List (CoprodI G))) lam :=
  fun _ _ _ _ _ => relativeLengthBound_of_eq_bot letterRelatorSubgroup_empty

/-- The empty family satisfies the torsion leaf outright. -/
theorem weightedTorsionLeaf_empty {L : RelativeLength G} {lam : ℚ} :
    WeightedTorsionLeaf L (∅ : Set (List (CoprodI G))) lam :=
  fun _ _ _ _ _ _ => torsionLifts_of_eq_bot letterRelatorSubgroup_empty

end Leaves

/-! ## 5.  The embedding clause, and the asymmetry that carries the lane -/

section Embedding

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- **The source factor stays embedded**, unconditionally on the length function
beyond its peripheral clause.

A difference of two source elements is a single letter, so the length bound would
have to produce a relator of fewer than two letters, and the design's floor is
`42`.  This is the weighted twin of
`OsinSmallCancellation.factorMap_injective_of_lengthBound`, and it is a theorem,
not a leaf.

Note what is **not** proved and must not be: the same statement at the partner
index.  There `L.len (CoprodI.of y)` is unbounded, the contradiction evaporates,
and `RelativeRouterEnvelope.exists_injective_to_partner` shows that if it did not
evaporate the source would embed in the partner. -/
theorem factorMap_source_injective {L : RelativeLength G}
    {R : Set (List (CoprodI G))} (hbound : RelativeLengthBound L R)
    (hfloor : ∀ r ∈ R, 2 ≤ r.length) :
    Function.Injective (factorMap (letterRelatorSubgroup R) false) := by
  intro x y hxy
  by_contra hne
  have hxy1 : x * y⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hof : CoprodI.of (x * y⁻¹) ≠ (1 : CoprodI G) := by
    intro h
    exact hxy1 (CoprodI.of_injective false (by rw [h, map_one]))
  have hmem : CoprodI.of (x * y⁻¹) ∈ letterRelatorSubgroup R := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : factorMap (letterRelatorSubgroup R) false (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact h1
  obtain ⟨r, hr, hlt⟩ := hbound _ hof hmem
  have h1 := L.len_source_le_one (x * y⁻¹)
  have h2 := hfloor r hr
  omega

end Embedding

/-! ## 6.  The weighted design -/

/-- **The weighted relative router design.**

The same shape as `RelativeRouterEnvelope.RelativeRouterDesign`, with three
changes: relators are letter lists rather than syllable words, the design carries
its relative length function, and **the tie is a field** — because at the weighted
metric it is no longer refuted.  The tie is what makes the partner's image fill
the quotient, and therefore what supplies property `(T)`. -/
structure WeightedRouterDesign (U B : Type) [Group U] [Group B]
    (G : Bool → Type) [∀ b, Group (G b)] where
  /-- The source factor is a copy of `U`. -/
  sourceEquiv : U ≃* G false
  /-- The partner factor is a copy of `B`. -/
  partnerEquiv : B ≃* G true
  /-- The relative length function, with its peripheral clause. -/
  relLength : RelativeLength G
  /-- The relator family, as letter lists. -/
  relators : Set (List (CoprodI G))
  /-- Finitely many relators — the finite-presentation obligation. -/
  relators_finite : relators.Finite
  /-- Every entry of every relator really is a letter. -/
  relators_letters : ∀ r ∈ relators, ∀ a ∈ r, relLength.len a ≤ 1
  /-- Closed under rotation and formal inversion. -/
  relators_symmetrized : LetterSymmetrized relators
  /-- No two cyclically adjacent letters cancel. -/
  relators_cyclicallyReduced : ∀ r ∈ relators, LetterCyclicallyReduced r
  /-- **The length floor**, now counted in letters — which is exactly what lets a
  tie relator meet it. -/
  relators_long : ∀ r ∈ relators, 42 ≤ r.length
  /-- No relator is a proper power. -/
  relators_noProperPower : LetterNoProperPower relators
  /-- The metric condition at the design's constant. -/
  metric : LetterMetricSmallCancellation relators (1 / 7)
  /-- The number of source generators. -/
  sourceCard : ℕ
  /-- The source generators. -/
  sourceGen : Fin sourceCard → G false
  /-- They generate the source factor. -/
  sourceGen_generates : Subgroup.closure (Set.range sourceGen) = ⊤
  /-- **The tie.**  Each source generator is identified, modulo the relators,
  with an element of the partner factor.  In the unweighted lane this field is
  refutable (`RelativeRouterEnvelope.not_partnerSurjective`); here the tie relator
  is one peripheral letter followed by a spelling of the partner element, so it
  meets the floor as soon as that element is long. -/
  tie : ∀ j : Fin sourceCard, ∃ y : G true,
    CoprodI.of (sourceGen j) * (CoprodI.of y)⁻¹ ∈ letterRelatorSubgroup relators

namespace WeightedRouterDesign

variable {U B : Type} [Group U] [Group B] {G : Bool → Type} [∀ b, Group (G b)]
  (D : WeightedRouterDesign U B G)

/-- **The routed quotient** `(U * B) / ⟪R⟫`. -/
abbrev Routed : Type := CoprodI G ⧸ letterRelatorSubgroup D.relators

/-- The fragment slack at the design's constant, from the letter floor. -/
theorem fragmentSlack : LetterFragmentSlack D.relators (1 / 7) :=
  letterFragmentSlack_of_le_seventh le_rfl D.relators_long

/-- The source's map into the routed quotient. -/
def emb : U →* D.Routed :=
  (factorMap (letterRelatorSubgroup D.relators) false).comp
    D.sourceEquiv.toMonoidHom

/-- The partner's map into the routed quotient. -/
def partnerHom : B →* D.Routed :=
  (factorMap (letterRelatorSubgroup D.relators) true).comp
    D.partnerEquiv.toMonoidHom

/-! ### The structural clauses, all leaf-free -/

/-- Both factors are torsion-free, transported from `U` and `B`. -/
theorem factors_torsionFree (hU : IsPowerTorsionFree U) (hB : IsPowerTorsionFree B) :
    ∀ b, IsPowerTorsionFree (G b) := by
  intro b
  cases b
  · exact IsPowerTorsionFree.comap hU D.sourceEquiv.symm.toMonoidHom
      D.sourceEquiv.symm.injective
  · exact IsPowerTorsionFree.comap hB D.partnerEquiv.symm.toMonoidHom
      D.partnerEquiv.symm.injective

/-- Both factors are finitely presented, transported from `U` and `B`. -/
theorem factors_finitelyPresented [Group.IsFinitelyPresented U]
    [Group.IsFinitelyPresented B] : ∀ b, Group.IsFinitelyPresented (G b) := by
  intro b
  cases b
  · exact Group.IsFinitelyPresented.equiv D.sourceEquiv
  · exact Group.IsFinitelyPresented.equiv D.partnerEquiv

/-- The ambient free product is finitely presented. -/
theorem ambient_finitelyPresented [Group.IsFinitelyPresented U]
    [Group.IsFinitelyPresented B] : Group.IsFinitelyPresented (CoprodI G) := by
  haveI : Group.IsFinitelyPresented (G false) := D.factors_finitelyPresented false
  haveI : Group.IsFinitelyPresented (G true) := D.factors_finitelyPresented true
  exact FreeProductRouterObstruction.isFinitelyPresented_coprodI_bool G

/-- The ambient free product is torsion-free. -/
theorem ambient_torsionFree (hU : IsPowerTorsionFree U) (hB : IsPowerTorsionFree B) :
    IsPowerTorsionFree (CoprodI G) :=
  isPowerTorsionFree_coprodI (D.factors_torsionFree hU hB)

/-- The relator subgroup is the normal closure of a finite set. -/
theorem letterRelatorSubgroup_finitelyNormallyGenerated :
    (letterRelatorSubgroup D.relators).IsFinitelyNormallyGenerated :=
  ⟨List.prod '' D.relators, D.relators_finite.image _, rfl⟩

/-- **Finite presentation of the routed quotient, derived**, spending no leaf. -/
theorem finitelyPresented [Group.IsFinitelyPresented U]
    [Group.IsFinitelyPresented B] : Group.IsFinitelyPresented D.Routed := by
  haveI := D.ambient_finitelyPresented
  exact Group.IsFinitelyPresented.quotient (letterRelatorSubgroup D.relators)
    D.letterRelatorSubgroup_finitelyNormallyGenerated

/-! ### Property `(T)`, now derived

The tie makes the partner's image fill the quotient, and `(T)` descends.  In the
unweighted lane this chain existed too — and refuted itself.  Here nothing
refutes it, because the tie relator is long in the relative metric. -/

/-- Every source syllable lies in the partner's image: the tie holds on a
generating set, and lying in the partner's image is a subgroup condition. -/
theorem mem_range_partnerHom_of_source (x : G false) :
    QuotientGroup.mk' (letterRelatorSubgroup D.relators) (CoprodI.of x)
      ∈ D.partnerHom.range := by
  have hsub : (⊤ : Subgroup (G false)) ≤
      (D.partnerHom.range).comap
        (factorMap (letterRelatorSubgroup D.relators) false) := by
    rw [← D.sourceGen_generates, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨y, hy⟩ := D.tie j
    refine ⟨D.partnerEquiv.symm y, ?_⟩
    have h1 : D.partnerHom (D.partnerEquiv.symm y)
        = QuotientGroup.mk' (letterRelatorSubgroup D.relators) (CoprodI.of y) := by
      show QuotientGroup.mk' (letterRelatorSubgroup D.relators)
        (CoprodI.of (D.partnerEquiv (D.partnerEquiv.symm y))) = _
      rw [MulEquiv.apply_symm_apply]
    rw [h1]
    exact (mk_eq_mk_of_mem hy).symm
  exact hsub (Subgroup.mem_top x)

/-- **The partner fills the quotient, derived from the tie.** -/
theorem partnerHom_surjective : Function.Surjective D.partnerHom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  rintro q -
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (letterRelatorSubgroup D.relators) q
  induction g using CoprodI.induction_on with
  | one =>
      rw [map_one]
      exact one_mem _
  | of b x =>
      cases b
      · exact D.mem_range_partnerHom_of_source x
      · refine ⟨D.partnerEquiv.symm x, ?_⟩
        show QuotientGroup.mk' (letterRelatorSubgroup D.relators)
          (CoprodI.of (D.partnerEquiv (D.partnerEquiv.symm x))) = _
        rw [MulEquiv.apply_symm_apply]
  | mul u v hu hv =>
      rw [map_mul]
      exact mul_mem hu hv

/-- **Property `(T)`, derived.**  No longer a hypothesis: the tie is legal at the
weighted metric, so the partner surjects and `(T)` descends. -/
theorem kazhdan (hB : HasKazhdanPropertyT.{0, 0} B) :
    HasKazhdanPropertyT.{0, 0} D.Routed :=
  HasKazhdanPropertyT.of_surjective D.partnerHom D.partnerHom_surjective hB

/-! ### The two clauses that spend a leaf -/

/-- The relative Greendlinger bound, from the length leaf. -/
theorem lengthBound
    (hleafG : WeightedGreendlingerLeaf D.relLength D.relators (1 / 7)) :
    RelativeLengthBound D.relLength D.relators :=
  hleafG D.relators_symmetrized D.relators_cyclicallyReduced D.relators_letters
    D.fragmentSlack D.metric

/-- **The source embeds**, from the length leaf and the peripheral clause. -/
theorem emb_injective
    (hleafG : WeightedGreendlingerLeaf D.relLength D.relators (1 / 7)) :
    Function.Injective D.emb := by
  have hfloor : ∀ r ∈ D.relators, 2 ≤ r.length := by
    intro r hr
    have h := D.relators_long r hr
    omega
  exact (factorMap_source_injective (D.lengthBound hleafG) hfloor).comp
    D.sourceEquiv.injective

/-- **The routed quotient is torsion-free**, from the torsion leaf and ambient
torsion-freeness — and, unlike the unweighted lane, with no demand that the
partner factor stay embedded. -/
theorem torsionFree (hleafT : WeightedTorsionLeaf D.relLength D.relators (1 / 7))
    (hU : IsPowerTorsionFree U) (hB : IsPowerTorsionFree B) :
    IsPowerTorsionFree D.Routed :=
  isPowerTorsionFree_of_torsionLifts (D.ambient_torsionFree hU hB)
    (hleafT D.relators_symmetrized D.relators_cyclicallyReduced
      D.relators_letters D.fragmentSlack D.metric D.relators_noProperPower)

/-! ## 7.  The envelope, with no property-`(T)` hypothesis -/

/-- **A Kazhdan envelope of `U` from a weighted relative router design.**

All four clauses are conclusions.  Compare
`RelativeRouterEnvelope.kazhdanEnvelope_of_design`, which carries property `(T)`
as a hypothesis because at the syllable metric the only route to it is refutable:
here the tie is a field of the design, the partner surjects, and `(T)` descends
from the certified partner.

What remains open is exactly the two weighted leaves. -/
noncomputable def kazhdanEnvelope_of_design [Group.IsFinitelyPresented U]
    [Group.IsFinitelyPresented B]
    (hleafG : WeightedGreendlingerLeaf D.relLength D.relators (1 / 7))
    (hleafT : WeightedTorsionLeaf D.relLength D.relators (1 / 7))
    (hU : IsPowerTorsionFree U) (hBtf : IsPowerTorsionFree B)
    (hBT : HasKazhdanPropertyT.{0, 0} B) : KazhdanEnvelope U where
  Carrier := D.Routed
  finitelyPresentedCarrier := D.finitelyPresented
  torsionFree := D.torsionFree hleafT hU hBtf
  kazhdan := D.kazhdan hBT
  emb := D.emb
  emb_injective := D.emb_injective hleafG

end WeightedRouterDesign

/-! ## 8.  The obstruction, lifted — and exactly where it still bites

The unweighted refutation is not repaired by fiat.  It is a theorem about short
elements of the relator subgroup, it survives verbatim, and what the weighted
metric changes is that a tie is no longer short. -/

section Obstruction

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- **The refutation, in its sharpest form.**  No element of the relator subgroup
can be shorter than half of every relator.  The unweighted collapse is this
theorem plus the fact that at the syllable metric a tie is two letters long. -/
theorem not_relativeLengthBound_of_short {L : RelativeLength G}
    {R : Set (List (CoprodI G))} {t : CoprodI G} (ht : t ≠ 1)
    (hmem : t ∈ letterRelatorSubgroup R)
    (hshort : ∀ r ∈ R, 2 * L.len t ≤ r.length) :
    ¬ RelativeLengthBound L R := by
  intro hb
  obtain ⟨r, hr, hlt⟩ := hb t ht hmem
  have h := hshort r hr
  omega

/-- **A tie is as long as the partner element it ties to**, up to the one letter
the source element costs.  This is the inequality the whole refinement turns on:
in the syllable metric the right-hand side is at most `1 + 1`, and in a genuine
`X ∪ U` metric it grows with the partner element. -/
theorem len_le_tie_succ (L : RelativeLength G) (x : G false) (y : G true) :
    L.len (CoprodI.of y)
      ≤ 1 + L.len (CoprodI.of x * (CoprodI.of y)⁻¹) := by
  have h1 : (CoprodI.of y : CoprodI G)⁻¹
      = (CoprodI.of x)⁻¹ * (CoprodI.of x * (CoprodI.of y)⁻¹) := by group
  have h2 := L.len_mul_le ((CoprodI.of x)⁻¹)
    (CoprodI.of x * (CoprodI.of y)⁻¹)
  rw [← h1, L.len_inv, L.len_inv] at h2
  have h3 := L.len_source_le_one x
  omega

/-- **The collapse, and precisely its hypothesis.**  A tie to a partner element
that is itself a single letter is short, and refutes the length bound against any
family with relators of four letters or more.

The hypothesis `hlight` is the whole of what the weighted metric removes.  It
holds for *every* partner element at the syllable model
(`syllableLength_partner_le_one`), which is why the unweighted lane collapses;
it holds for no long partner element in an `X ∪ U` metric. -/
theorem not_relativeLengthBound_of_light_tie {L : RelativeLength G}
    {R : Set (List (CoprodI G))} {x : G false} {y : G true} (hx : x ≠ 1)
    (hlight : L.len (CoprodI.of y) ≤ 1) (hfloor : ∀ r ∈ R, 4 ≤ r.length)
    (htie : CoprodI.of x * (CoprodI.of y)⁻¹ ∈ letterRelatorSubgroup R) :
    ¬ RelativeLengthBound L R := by
  refine not_relativeLengthBound_of_short
    (RelativeRouterEnvelope.tieWord_ne_one hx y) htie ?_
  intro r hr
  have hsub := L.len_mul_le (CoprodI.of x) ((CoprodI.of y)⁻¹)
  have hinv : L.len ((CoprodI.of y : CoprodI G)⁻¹) = L.len (CoprodI.of y) :=
    L.len_inv _
  have hsrc := L.len_source_le_one x
  have hfl := hfloor r hr
  omega

end Obstruction

section SyllableCollapse

variable {G : Bool → Type} [∀ b, Group (G b)] [∀ b, DecidableEq (G b)]

/-- **The previous lane, recovered as the degenerate case.**  At the syllable
model every partner element is light, so every tie refutes the length bound.
This is `RelativeRouterEnvelope.not_partnerSurjective` in the vocabulary of this
file, and it says the unweighted design's tie field is uninhabitable — while the
weighted design carries it as a field. -/
theorem not_relativeLengthBound_of_tie_syllableModel
    {R : Set (List (CoprodI G))} {x : G false} {y : G true} (hx : x ≠ 1)
    (hfloor : ∀ r ∈ R, 4 ≤ r.length)
    (htie : CoprodI.of x * (CoprodI.of y)⁻¹ ∈ letterRelatorSubgroup R) :
    ¬ RelativeLengthBound (syllableLength G) R :=
  not_relativeLengthBound_of_light_tie hx (syllableLength_partner_le_one G y)
    hfloor htie

end SyllableCollapse

/-! ## 9.  The canonical model: Osin's alphabet `X ∪ U`

`Algebra.WordMetric` already builds the word length of a symmetric generating set
and proves its four laws, so the model is six lines once the alphabet is named.
`osinAlphabet` is that alphabet: every element of the source factor, together
with the partner's generators and their inverses. -/

section AlphabetModel

variable {G : Bool → Type} [∀ b, Group (G b)]

/-- **A relative length function from a symmetric generating set.**  The four
length laws are `Algebra.WordMetric`'s; the peripheral clause is the demand that
every source element be a letter of the alphabet. -/
noncomputable def ofSymmetricGeneratingSet {S : Set (CoprodI G)}
    (hS : WordMetric.IsSymmetricGeneratingSet S)
    (hsrc : ∀ x : G false, CoprodI.of x ∈ S) : RelativeLength G where
  len := WordMetric.wordNorm S
  len_one := WordMetric.wordNorm_one S
  eq_one_of_len_eq_zero := fun g h => (WordMetric.wordNorm_eq_zero_iff hS g).mp h
  len_mul_le := WordMetric.wordNorm_mul_le hS
  len_inv := WordMetric.wordNorm_inv hS
  len_source_le_one := fun x => WordMetric.wordNorm_le_one_of_mem (hsrc x)

/-- **Osin's alphabet** `X ∪ U`: the whole source factor, plus the partner's
generators and their inverses. -/
def osinAlphabet (G : Bool → Type) [∀ b, Group (G b)] {k : ℕ}
    (gen : Fin k → G true) : Set (CoprodI G) :=
  (Set.range fun x : G false => CoprodI.of x) ∪
      (Set.range fun j : Fin k => CoprodI.of (gen j)) ∪
    (Set.range fun j : Fin k => (CoprodI.of (gen j))⁻¹)

/-- **The alphabet is a symmetric generating set.**  Symmetry is three cases;
generation is that the source factor is contained outright and the partner factor
is generated by `gen`, and that the two factors generate the free product. -/
theorem isSymmetricGeneratingSet_osinAlphabet {k : ℕ} (gen : Fin k → G true)
    (hgen : Subgroup.closure (Set.range gen) = ⊤) :
    WordMetric.IsSymmetricGeneratingSet (osinAlphabet G gen) := by
  constructor
  · rintro a ((⟨x, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · exact Or.inl (Or.inl ⟨x⁻¹, by simp⟩)
    · exact Or.inr ⟨j, rfl⟩
    · exact Or.inl (Or.inr ⟨j, by simp⟩)
  · rw [eq_top_iff]
    rintro g -
    induction g using CoprodI.induction_on with
    | one => exact one_mem _
    | of b x =>
        cases b
        · exact Subgroup.subset_closure (Or.inl (Or.inl ⟨x, rfl⟩))
        · have hle : Subgroup.closure (Set.range gen) ≤
              (Subgroup.closure (osinAlphabet G gen)).comap
                (CoprodI.of : G true →* CoprodI G) := by
            rw [Subgroup.closure_le]
            rintro _ ⟨j, rfl⟩
            exact Subgroup.subset_closure (Or.inl (Or.inr ⟨j, rfl⟩))
          rw [hgen] at hle
          exact hle (Subgroup.mem_top x)
    | mul u v hu hv => exact mul_mem hu hv

/-- **The canonical relative length function**, on `U * B` with the partner
spelled in a finite generating set.  Every clause is proved; nothing is assumed.

This is the model the whole lane is designed for, and the one in which a tie
relator `u · w⁻¹` has length `1 + |w|_X` and meets the floor. -/
noncomputable def osinLength {k : ℕ} (gen : Fin k → G true)
    (hgen : Subgroup.closure (Set.range gen) = ⊤) : RelativeLength G :=
  ofSymmetricGeneratingSet (isSymmetricGeneratingSet_osinAlphabet gen hgen)
    (fun x => Or.inl (Or.inl ⟨x, rfl⟩))

/-- The partner's generators are letters, so a relator spelled in them meets the
`relators_letters` field of a design. -/
theorem osinLength_gen_le_one {k : ℕ} (gen : Fin k → G true)
    (hgen : Subgroup.closure (Set.range gen) = ⊤) (j : Fin k) :
    (osinLength gen hgen).len (CoprodI.of (gen j)) ≤ 1 :=
  WordMetric.wordNorm_le_one_of_mem (Or.inl (Or.inr ⟨j, rfl⟩))

/-- The inverses of the partner's generators are letters too. -/
theorem osinLength_gen_inv_le_one {k : ℕ} (gen : Fin k → G true)
    (hgen : Subgroup.closure (Set.range gen) = ⊤) (j : Fin k) :
    (osinLength gen hgen).len ((CoprodI.of (gen j))⁻¹) ≤ 1 :=
  WordMetric.wordNorm_le_one_of_mem (Or.inr ⟨j, rfl⟩)

end AlphabetModel

/-! ## 10.  The certified partner, and the alphabet it supplies

`CongruenceSubgroup.gamma3Partner` is finitely presented, so
`RelativeRouterEnvelope.finiteGeneration` extracts a finite generating tuple by
choice; that tuple is the `X` of `osinAlphabet`, and `osinLength` is then the
relative metric of `U * Γ(3)` relative to `{U}`. -/

/-- The partner's generating tuple, at the type `osinAlphabet` consumes: the `X`
of the alphabet `X ∪ U`.

The partner's other two fields are not restated here —
`RelativeRouterEnvelope.gamma3_kazhdan` and
`RelativeRouterEnvelope.gamma3_torsionFree` already name them at the types
`kazhdanEnvelope_of_design` consumes, and this module imports that one.  The
difference is where they are spent: there property `(T)` of the *partner* was
carried but unusable, since the surjection it needed was refutable; here it is
spent through `WeightedRouterDesign.kazhdan`. -/
noncomputable def gamma3Gen :
    RelativeRouterEnvelope.FiniteGeneration CongruenceSubgroup.gamma3Partner.B :=
  RelativeRouterEnvelope.gamma3Generation

end OsinWeightedMetric
end GroupApproximation
