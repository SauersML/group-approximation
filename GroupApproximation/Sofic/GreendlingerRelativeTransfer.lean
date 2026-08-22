import GroupApproximation.Sofic.OsinRelativeSmallCancellation
import Mathlib.Data.List.Rotate

/-!
# The relative transfer: from the metric condition to the two named predicates

`Sofic.OsinRelativeSmallCancellation` proves the consequence layer of Osin's
two clauses over a free product — the peripheral factor stays embedded, the
quotient stays torsion-free — conditional on two predicates on the relator
family, `GreendlingerLengthBound` and `TorsionIntoFactors`.  This file is the
transfer that feeds them: it fixes the hypotheses under which the metric
small-cancellation condition delivers both, cuts each of the two remaining
implications down to the smallest statement that still buys it, and assembles
the single theorem the router construction consumes.

## The consumption point

`osin_conclusion_of_metric` — one theorem, four conclusions: the length bound,
the torsion classification, the embedding clause for *every* factor, and
torsion-freeness of the quotient.  A caller supplying a relator family, its
design certificates and the two open leaves gets the whole conclusion list of
the relative small-cancellation theorem with no further plumbing.

## What is open, and in what form

Two leaves, each a named predicate carrying its own design hypotheses, so that
every consumption point names the leaf it spends and nothing propagates
silently:

* `RelativeGreendlingerLeaf` — the relative Greendlinger lemma, **stated at the
  length form**, `GreendlingerLengthBound R`.  Not at the subword form: nothing
  downstream of this file reads the subword, and the length form is strictly
  weaker (`relativeGreendlingerLeaf_of_subword` records the implication).
* `RelativeTorsionLeaf` — the relative torsion classification, **stated at root
  closure on cyclically reduced words**, `CyclicPowerRootClosed R`, which
  mentions the quotient nowhere.

Both leaves are inhabited: `relativeGreendlingerLeaf_empty` and
`relativeTorsionLeaf_empty` discharge the empty family outright, so
`osin_conclusion_of_metric_empty` spends no leaf at all.

## The reductions, all proved

Each leaf is cut down before it is stated, so what a diagram argument has to
supply is as small as this file can make it.

* `torsionIntoFactors_of_cyclicTorsionIntoFactors` — **the quantifier over the
  quotient, discharged.**  Cyclic reduction splits an arbitrary quotient element
  into three kinds; two settle themselves (the identity, and a conjugate of a
  syllable, which is literally the conclusion), so the only case a diagram
  argument ever sees is a cyclically reduced word.
* `cyclicTorsionIntoFactors_of_rootClosed` and
  `rootClosed_of_cyclicTorsionIntoFactors` — **root closure is the same
  statement**, over torsion-free factors, and it mentions no quotient.
* `cyclicPowerRootClosed_iff_prime` — **root closure at prime exponents is
  enough.**  A composite exponent factors as `n = m·p` with `p` prime, and
  `uᵐ` is again cyclically reduced (`FreeProductCyclic.npow`), so a strong
  induction on the exponent reduces the general statement to the prime one —
  which is the exponent the classical annular argument is run at.  Both
  directions are proved.
* `greendlingerLengthBound_iff` — **the length bound splits into two
  independent halves**, and both directions are proved:

      GreendlingerLengthBound R  ↔  CyclicLengthBound R ∧ NoShortRelation R

  `CyclicLengthBound` is the bound asked only of cyclically reduced words —
  the same quantifier discharge the torsion clause gets — and `NoShortRelation`
  says the relator subgroup contains no nontrivial element of one syllable.
  The split is not cosmetic: `factorMap_injective_of_noShortRelation` shows the
  **embedding clause needs only the short half**, with no length bound anywhere,
  and the `ℤ * ℤ/3` witness recorded below refutes exactly that half.
* `cyclicLengthBound_at_conj` — **the one-conjugate case, at the residual.**  A
  cyclically reduced word conjugate to a relator already satisfies the cyclic
  bound, with the sharp constant: `wlen_le_sylLength_conj` gives `|r| ≤ |g|`,
  never merely `|r| < 2|g|`.  What is left of the leaf is therefore expressions
  with two or more conjugate factors, and nothing else.
* `noProperPower_of_prime_wlen` — **a designable criterion for the
  no-proper-power hypothesis.**  A cyclically reduced relator whose syllable
  length is prime is not a proper power, because a proper power's cyclically
  reduced form has length `k · |u|` with both factors at least two, and syllable
  length of the cyclically reduced form is a conjugacy invariant
  (`FreeProductCyclic.length_eq_of_conj`).  So the hypothesis is checkable by
  counting syllables, and the relator design can meet it by construction.

## Three hypotheses that are not decoration

The implication as displayed in the docstring of
`OsinRelativeSmallCancellation` — `MetricSmallCancellation R (1/6) →
GreendlingerLengthBound R` and `→ TorsionIntoFactors (relatorSubgroup R)` — is
false without three further hypotheses, and each has a witness.

* **Symmetrization** (`Symmetrized`).  `IsPiece R` compares *distinct members of
  `R`*, so a one-element family has no pieces at all and satisfies
  `MetricSmallCancellation R lam` vacuously for every `lam`, while Dehn's
  algorithm needs every rotation and every formal inverse of a relator to be
  available as a competing occurrence.  The free-group side of the same program
  takes this route explicitly: `SmallCancellationRouter` measures pieces in
  `symmetrization R` and never in `R`.  Here symmetrization is a hypothesis on
  `R` rather than a closure operator, because rotating a `Word G` means
  rebuilding it letter by letter, and the router's relator family will be
  presented symmetrized already.

* **No relator is a proper power** (`NoProperPower`).  `C'(1/6)` does not imply a
  torsion-free quotient, over a free product or over a free group.  Take
  `G₀ = G₁ = ℤ` with generators `x, y` and the symmetrized family of `(xy)^7`:
  its rotations by an even number of syllables are the word itself, the odd
  rotations begin in the other factor, and the inverses begin with inverse
  letters, so *no two distinct members share even one syllable of prefix* — the
  family is `C'(lam)` for every positive `lam`, vacuously — and the image of `xy`
  in the quotient has order `7`.  Since the factors are torsion-free and (by the
  embedding clause) stay embedded, that element is not conjugate to the image of
  any factor element, so `TorsionIntoFactors` fails outright.  This is
  Lyndon--Schupp Ch. V, Thm 10.1 read backwards: in a `C'(1/6)` group the torsion
  is *exactly* the conjugates of powers of the roots of relators, and it is empty
  precisely when no relator is a proper power.

* **Long relators, and `1/7` rather than `1/6`** (`hlong`, and the constant in
  `hmetric`).  Pieces here are whole syllables: `IsPiece R p` asks for `p` to be
  a prefix of two relators *as syllable lists*.  Over a free product the
  classical piece may also end in a *fragment* of a syllable — `u = u₁u₂` with
  only `u₁` shared — and Lyndon--Schupp count that fragment as a full syllable of
  the piece.  So the classical family of pieces is strictly larger, and the
  in-repo condition is the *weaker* of the two, not the stronger: a
  whole-syllable piece of length `k` extends to a classical piece of length
  `k + 1`, no more, since truncating a classical piece to its complete syllables
  gives a whole-syllable piece.  Hence whole-syllable `C'(lam)` gives classical
  `C'(lam + 1/|r|)`, and

      lam = 1/7  and  |r| ≥ 42   ⟹   lam + 1/|r| ≤ 1/7 + 1/42 = 1/6,

  which is the classical hypothesis with room to spare.  Both numbers are free
  design parameters for a Rips-style relator family — long blocks with disjoint
  ranges are what such a family is made of — so nothing downstream pays for the
  correction.  `FragmentSlack` states the inequality once and
  `fragmentSlack_of_le_seventh` is the only place the two numbers appear, so a
  caller may substitute any pair with `lam < 1/6` and `|r| ≥ 1 / (1/6 - lam)`.
  What *cannot* be substituted is `lam = 1/6` with a length hypothesis: the slack
  inequality fails there for every length, so lowering the constant is not
  optional.  A fragment-aware `IsPiece` would let the constant be `1/6` and
  delete the length hypothesis; that is a refinement of the *definitions* in
  `OsinRelativeSmallCancellation`, not of anything proved here.

  The bare implication has an explicit refutation, found by the router
  construction: over `ℤ * ℤ/3` with generators `e` and `b`, the symmetrized
  family of the two-syllable relator `e·b⁻¹` has pairwise distinct first
  syllables — `e`, `b⁻¹`, `b`, `e⁻¹` — hence no nonempty whole-syllable piece at
  all, so `MetricSmallCancellation R (1/6)` holds vacuously; but `e ≡ b` in the
  quotient forces `of (e³)` into the relator subgroup, an element of syllable
  length one, and the length bound would need a relator shorter than two
  syllables.  In the vocabulary of `greendlingerLengthBound_iff` that witness
  refutes `NoShortRelation` and says nothing about `CyclicLengthBound`: it is the
  short half of the length bound, and only that half, which any relator length
  hypothesis kills.  The slack inequality guards something else, and at every
  length, because the classical count needs classical pieces.

**This module's two leaves are open, and every theorem that spends one names it
in its binder list.**  Nothing here is a structure or a hypothesis package: the
leaves are predicates on the relator family, in the same style as
`GreendlingerLengthBound` and `TorsionIntoFactors` themselves, so a caller can
see at the call site exactly what is being assumed — and every proof in this file
is complete, so the module carries no incompleteness into anything that imports
it.  What an importer must do instead is discharge the leaf it names, and the
name is in the statement it applies.  `scripts/Audit.lean`'s axiom probe remains
the gate of record.
-/

namespace GroupApproximation
namespace GreendlingerRelativeTransfer

open Monoid Monoid.CoprodI OsinSmallCancellation

section Transfer

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-! ## 1.  The design hypotheses on a relator family -/

/-- The syllable list of the formal inverse of a word: invert every letter and
read the list backwards. -/
def invSyllables (l : List (Σ i, G i)) : List (Σ i, G i) :=
  (l.map fun p => (⟨p.1, p.2⁻¹⟩ : Σ i, G i)).reverse

/-- **The family is symmetrized**: every cyclic rotation of a relator, and every
rotation of a relator's formal inverse, is again a relator.

Stated as membership of *any* word spelling the rotated list, so that a caller
never has to produce a canonical rotated `Word`: the reduced-word invariants
determine a `Word` from its syllable list, so the two readings agree. -/
def Symmetrized (R : Set (Word G)) : Prop :=
  (∀ r ∈ R, ∀ (n : ℕ) (w : Word G), w.toList = r.toList.rotate n → w ∈ R) ∧
    (∀ r ∈ R, ∀ (n : ℕ) (w : Word G),
      w.toList = (invSyllables r.toList).rotate n → w ∈ R)

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
theorem symmetrized_empty : Symmetrized (∅ : Set (Word G)) := by
  constructor <;> intro r hr <;> simp at hr

/-- **No relator is a proper power.**  Without this the quotient acquires torsion
of its own: see the `(xy)^7` witness in the module docstring. -/
def NoProperPower (R : Set (Word G)) : Prop :=
  ∀ r ∈ R, ∀ (s : CoprodI G) (k : ℕ), 2 ≤ k → r.prod ≠ s ^ k

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
theorem noProperPower_empty : NoProperPower (∅ : Set (Word G)) := by
  intro r hr
  simp at hr

/-- **A prime syllable count rules out proper powers.**

A proper power `s ^ k` is conjugate to `u ^ k` for a cyclically reduced `u`, and
`|u ^ k| = k · |u|` on the nose, so the cyclically reduced length of a proper
power factors with both factors at least two.  Syllable length of a cyclically
reduced form is a conjugacy invariant, so that factorization is a factorization
of `wlen r` — impossible for a prime.

This is the criterion a relator design can meet by counting: choose the block
structure so that every relator has a prime number of syllables. -/
theorem noProperPower_of_prime_wlen {R : Set (Word G)}
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hprime : ∀ r ∈ R, Nat.Prime (wlen r)) : NoProperPower R := by
  intro r hr s k hk heq
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨i, j, u, hij, hu⟩ := hcyc r hr
  have hprod : u.prod = r.prod := congrArg Word.prod hu
  have hlist : u.toList = r.toList := congrArg Word.toList hu
  rcases FreeProductCyclic.exists_cyclicReduction s with
    h1 | ⟨p, x, c, hs⟩ | ⟨p, q, v, c, hpq, hs⟩
  · exact FreeProductCyclic.pow_ne_one_of_ne hij u 0
      (by rw [zero_add, pow_one, hprod, heq, h1, one_pow])
  · exact FreeProductCyclic.not_conj_of_le_one hij u (x ^ (m + 1)) c
      (by rw [hprod, heq, hs, FreeProductCyclic.conj_pow_eq, map_pow])
  · have hpow : u.prod = c * (FreeProductCyclic.npow hpq v m).prod * c⁻¹ := by
      rw [FreeProductCyclic.npow_prod, hprod, heq, hs,
        FreeProductCyclic.conj_pow_eq]
    have hlen := FreeProductCyclic.length_eq_of_conj hpq hij
      (FreeProductCyclic.npow hpq v m) u c hpow
    rw [FreeProductCyclic.npow_toList_length, hlist] at hlen
    have hwlen : wlen r = (m + 1) * v.toList.length := hlen.symm
    have h2 : 2 ≤ v.toList.length := FreeProductCyclic.two_le_length_of_ne hpq v
    have hp := hprime r hr
    rcases hp.eq_one_or_self_of_dvd (m + 1) ⟨v.toList.length, hwlen⟩ with h | h
    · omega
    · rw [h] at hwlen
      have hmul : wlen r * 2 ≤ wlen r * v.toList.length :=
        Nat.mul_le_mul (le_refl _) h2
      rw [← hwlen] at hmul
      have := hp.two_le
      omega

/-! ## 2.  The torsion clause, cut to root closure at a prime -/

/-- **Osin's torsion clause, restricted to cyclically reduced words.**  The same
disjunction as `TorsionIntoFactors`, asked only of the image of a word whose
first and last syllables lie in different factors.

The disjunction is not "the word is in the relator subgroup": over a free product
with torsion in the factors it must not be.  With `G₀ = ℤ/7 = ⟨x⟩`, `G₁ = ℤ = ⟨y⟩`
and the symmetrized family of the two-syllable relator `xy`, the cyclically
reduced word `x y²` has image `y = x⁻¹` in the quotient, whose seventh power is
trivial while the word itself is not in the relator subgroup.  It *is* conjugate
to the image of a factor element, which is exactly what the second disjunct
says. -/
def CyclicTorsionIntoFactors (R : Set (Word G)) : Prop :=
  ∀ (i j : ι) (u : NeWord G i j), i ≠ j → ∀ n : ℕ, 0 < n →
    u.prod ^ n ∈ relatorSubgroup R →
      QuotientGroup.mk' (relatorSubgroup R) u.prod = 1 ∨
        ∃ (p : ι) (x : G p) (d : CoprodI G ⧸ relatorSubgroup R),
          QuotientGroup.mk' (relatorSubgroup R) u.prod
            = d * factorMap (relatorSubgroup R) p x * d⁻¹

/-- **The quantifier over the quotient, discharged.**  Cyclic reduction sorts
every element of the free product into three kinds; the identity and the
conjugates of a single syllable *are* the conclusion, and the cyclically reduced
case is passed on.  So a proof of the torsion clause never has to look at a word
that is not cyclically reduced. -/
theorem torsionIntoFactors_of_cyclicTorsionIntoFactors {R : Set (Word G)}
    (hcyclic : CyclicTorsionIntoFactors R) :
    TorsionIntoFactors (relatorSubgroup R) := by
  classical
  intro q n hn hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := relatorSubgroup R) q
  have hgn : g ^ n ∈ relatorSubgroup R := by
    have h2 : QuotientGroup.mk' (relatorSubgroup R) (g ^ n) = 1 := by
      rw [map_pow]; exact hq
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h2
    exact h2
  rcases FreeProductCyclic.exists_cyclicReduction g with
    h1 | ⟨i, x, c, hgc⟩ | ⟨i, j, u, c, hij, hgc⟩
  · left
    rw [h1, map_one]
  · right
    refine ⟨i, x, QuotientGroup.mk' (relatorSubgroup R) c, ?_⟩
    rw [hgc]
    simp only [map_mul, map_inv, factorMap_apply]
  · have hconj : c * u.prod ^ n * c⁻¹ ∈ relatorSubgroup R := by
      rw [← FreeProductCyclic.conj_pow_eq, ← hgc]
      exact hgn
    have hupow : u.prod ^ n ∈ relatorSubgroup R := by
      have h := (relatorSubgroup_normal R).conj_mem _ hconj c⁻¹
      rwa [show c⁻¹ * (c * u.prod ^ n * c⁻¹) * c⁻¹⁻¹ = u.prod ^ n by group] at h
    rcases hcyclic i j u hij n hn hupow with h1 | ⟨p, x, d, hd⟩
    · left
      rw [hgc]
      simp only [map_mul, map_inv, h1]
      group
    · right
      refine ⟨p, x, QuotientGroup.mk' (relatorSubgroup R) c * d, ?_⟩
      rw [hgc]
      simp only [map_mul, map_inv, hd]
      group

/-- **Root closure on cyclically reduced words**: a cyclically reduced word with
a positive power in the relator subgroup is itself in the relator subgroup.

Over torsion-free factors this is an equivalent form of
`CyclicTorsionIntoFactors` (both directions below), and it is the form to aim a
proof at: it mentions the quotient nowhere.  It is *not* equivalent in general —
the `ℤ/7` witness in the docstring of `CyclicTorsionIntoFactors` satisfies that
predicate and refutes this one — so the equivalence is spent against the
torsion-freeness of the factors, exactly once. -/
def CyclicPowerRootClosed (R : Set (Word G)) : Prop :=
  ∀ (i j : ι) (u : NeWord G i j), i ≠ j → ∀ n : ℕ, 0 < n →
    u.prod ^ n ∈ relatorSubgroup R → u.prod ∈ relatorSubgroup R

/-- **Root closure at a prime exponent**, which is the exponent the classical
annular argument is run at. -/
def CyclicPrimeRootClosed (R : Set (Word G)) : Prop :=
  ∀ (i j : ι) (u : NeWord G i j), i ≠ j → ∀ p : ℕ, Nat.Prime p →
    u.prod ^ p ∈ relatorSubgroup R → u.prod ∈ relatorSubgroup R

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- A prime is a positive exponent, so the general form restricts. -/
theorem cyclicPrimeRootClosed_of_powerRootClosed {R : Set (Word G)}
    (h : CyclicPowerRootClosed R) : CyclicPrimeRootClosed R :=
  fun i j u hij p hp hu => h i j u hij p hp.pos hu

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- **Prime exponents are enough.**  A composite exponent factors as `n = m·p`
with `p` prime and `m` strictly smaller, and `uᵐ` is again a cyclically reduced
word (`FreeProductCyclic.npow` spells it with no cancellation), so the prime case
strips one factor and a strong induction on the exponent strips the rest.

This halves what the annular diagram argument has to carry: it may assume the
exponent is prime, which is what makes the classical count work. -/
theorem cyclicPowerRootClosed_of_prime {R : Set (Word G)}
    (h : CyclicPrimeRootClosed R) : CyclicPowerRootClosed R := by
  intro i j u hij n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hu
    rcases eq_or_ne n 1 with rfl | hne
    · rwa [pow_one] at hu
    obtain ⟨p, hp, m, rfl⟩ : ∃ p, Nat.Prime p ∧ ∃ m, n = m * p := by
      obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne
      obtain ⟨m, hm⟩ := hdvd
      exact ⟨p, hp, m, by rw [hm, Nat.mul_comm]⟩
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · omega
      · exact hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hlt : k + 1 < (k + 1) * p := by
      have h2 : 2 ≤ p := hp.two_le
      have hmul : (k + 1) * 2 ≤ (k + 1) * p := Nat.mul_le_mul (le_refl (k + 1)) h2
      have hstep : k + 1 < (k + 1) * 2 := by omega
      exact lt_of_lt_of_le hstep hmul
    have hnp : (FreeProductCyclic.npow hij u k).prod = u.prod ^ (k + 1) :=
      FreeProductCyclic.npow_prod hij u k
    have hmem : (FreeProductCyclic.npow hij u k).prod ^ p ∈ relatorSubgroup R := by
      rw [hnp, ← pow_mul]
      exact hu
    have hroot := h i j (FreeProductCyclic.npow hij u k) hij p hp hmem
    rw [hnp] at hroot
    exact ih (k + 1) hlt (by omega) hroot

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- **Root closure is root closure at primes.** -/
theorem cyclicPowerRootClosed_iff_prime {R : Set (Word G)} :
    CyclicPowerRootClosed R ↔ CyclicPrimeRootClosed R :=
  ⟨cyclicPrimeRootClosed_of_powerRootClosed, cyclicPowerRootClosed_of_prime⟩

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- Root closure is the stronger predicate, unconditionally. -/
theorem cyclicTorsionIntoFactors_of_rootClosed {R : Set (Word G)}
    (h : CyclicPowerRootClosed R) : CyclicTorsionIntoFactors R := by
  intro i j u hij n hn hu
  left
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact h i j u hij n hn hu

/-- **The converse, over torsion-free factors.**  The second disjunct of
`CyclicTorsionIntoFactors` names a factor element whose `n`-th power dies in the
quotient; the embedding clause carries that back to the factor, where
torsion-freeness kills it, and the disjunct collapses into the first. -/
theorem rootClosed_of_cyclicTorsionIntoFactors {R : Set (Word G)}
    (hlen : GreendlingerLengthBound R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hfree : ∀ i, IsPowerTorsionFree (G i)) (h : CyclicTorsionIntoFactors R) :
    CyclicPowerRootClosed R := by
  intro i j u hij n hn hu
  have hone : QuotientGroup.mk' (relatorSubgroup R) u.prod = 1 := by
    rcases h i j u hij n hn hu with h1 | ⟨p, x, d, hd⟩
    · exact h1
    · have hpow : (QuotientGroup.mk' (relatorSubgroup R) u.prod) ^ n = 1 := by
        rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hu
      rw [hd, FreeProductCyclic.conj_pow_eq] at hpow
      have h2 : (factorMap (relatorSubgroup R) p x) ^ n = 1 :=
        FreeProductCyclic.eq_one_of_conj_eq_one hpow
      have h3 : factorMap (relatorSubgroup R) p (x ^ n) = 1 := by
        rw [map_pow]; exact h2
      have h4 : x ^ n = 1 := by
        apply factorMap_injective_of_cyclicallyReduced hlen hcyc p
        rw [h3, map_one]
      rw [hd, hfree p x n hn h4, map_one, mul_one, mul_inv_cancel]
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hone
  exact hone

/-- **The degenerate family, discharged outright.**  With no relators a positive
power of a cyclically reduced word is never trivial
(`FreeProductCyclic.pow_ne_one_of_ne`), so the hypothesis of root closure is
never met. -/
theorem cyclicPowerRootClosed_of_eq_bot {R : Set (Word G)}
    (hR : relatorSubgroup R = ⊥) : CyclicPowerRootClosed R := by
  intro i j u hij n hn hu
  exfalso
  rw [hR, Subgroup.mem_bot] at hu
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact FreeProductCyclic.pow_ne_one_of_ne hij u m hu

/-! ## 3.  The length bound, split into two independent halves -/

/-- **The length bound, asked only of cyclically reduced words.**  The same
quantifier discharge the torsion clause gets from
`torsionIntoFactors_of_cyclicTorsionIntoFactors`. -/
def CyclicLengthBound (R : Set (Word G)) : Prop :=
  ∀ (i j : ι) (u : NeWord G i j), i ≠ j → u.prod ∈ relatorSubgroup R →
    ∃ r ∈ R, wlen r < 2 * FreeProductCyclic.sylLength u.prod

/-- **The relator subgroup contains no short relation**: an element of at most
one syllable lying in it is trivial.

This is the half of the length bound that the `ℤ * ℤ/3` witness of the module
docstring refutes, and — by `factorMap_injective_of_noShortRelation` — it is the
only half the embedding clause needs. -/
def NoShortRelation (R : Set (Word G)) : Prop :=
  ∀ g ∈ relatorSubgroup R, FreeProductCyclic.sylLength g ≤ 1 → g = 1

/-- **The Greendlinger bound for a single conjugate, with slack.**  A conjugate
of a cyclically reduced relator is at least as long as the relator
(`wlen_le_sylLength_conj`, sharp constant `1`), and a cyclically reduced relator
has at least two syllables, so the half-length bound holds with room. -/
theorem wlen_lt_two_mul_sylLength_conj {r : Word G} (hr : IsCyclicallyReduced r)
    (c : CoprodI G) :
    wlen r < 2 * FreeProductCyclic.sylLength (c * r.prod * c⁻¹) := by
  have h1 := wlen_le_sylLength_conj hr c
  have h2 := two_le_wlen hr
  omega

/-- **The one-conjugate case of the cyclic bound, closed.**  A cyclically reduced
word conjugate to a single relator already satisfies the bound, unconditionally.
What is left of `CyclicLengthBound` is therefore products of two or more
conjugates, and nothing else. -/
theorem cyclicLengthBound_at_conj {R : Set (Word G)} {i j : ι} {u : NeWord G i j}
    {r : Word G} (hr : r ∈ R) (hcyc : IsCyclicallyReduced r) {c : CoprodI G}
    (hconj : u.prod = c * r.prod * c⁻¹) :
    ∃ r' ∈ R, wlen r' < 2 * FreeProductCyclic.sylLength u.prod := by
  refine ⟨r, hr, ?_⟩
  rw [hconj]
  exact wlen_lt_two_mul_sylLength_conj hcyc c

/-- **The two halves put the length bound back together.**  Cyclic reduction
sorts a nontrivial element of the relator subgroup into a conjugate of a syllable
— killed by `NoShortRelation` — or a conjugate of a cyclically reduced word,
where `CyclicLengthBound` applies and conjugation only lengthens
(`FreeProductCyclic.length_le_sylLength_conj`). -/
theorem greendlingerLengthBound_of_cyclic {R : Set (Word G)}
    (hcy : CyclicLengthBound R) (hsh : NoShortRelation R) :
    GreendlingerLengthBound R := by
  intro g hg hmem
  rcases FreeProductCyclic.exists_cyclicReduction g with
    h1 | ⟨i, x, c, hgc⟩ | ⟨i, j, u, c, hij, hgc⟩
  · exact absurd h1 hg
  · exfalso
    apply hg
    have hmem' : c * CoprodI.of x * c⁻¹ ∈ relatorSubgroup R := by
      rw [← hgc]; exact hmem
    have hof : CoprodI.of x ∈ relatorSubgroup R := by
      have h := (relatorSubgroup_normal R).conj_mem _ hmem' c⁻¹
      rwa [show c⁻¹ * (c * CoprodI.of x * c⁻¹) * c⁻¹⁻¹ = CoprodI.of x by group] at h
    have hx1 : CoprodI.of x = 1 :=
      hsh _ hof (FreeProductCyclic.sylLength_of_le_one x)
    rw [hgc, hx1, mul_one, mul_inv_cancel]
  · have hmem' : c * u.prod * c⁻¹ ∈ relatorSubgroup R := by
      rw [← hgc]; exact hmem
    have hu : u.prod ∈ relatorSubgroup R := by
      have h := (relatorSubgroup_normal R).conj_mem _ hmem' c⁻¹
      rwa [show c⁻¹ * (c * u.prod * c⁻¹) * c⁻¹⁻¹ = u.prod by group] at h
    obtain ⟨r, hr, hlt⟩ := hcy i j u hij hu
    refine ⟨r, hr, ?_⟩
    have hsl : FreeProductCyclic.sylLength u.prod = u.toList.length := by
      apply FreeProductCyclic.sylLength_eq_of_neWord
      exact (FreeProductCyclic.equiv_prod _).symm
    have hle : u.toList.length ≤ FreeProductCyclic.sylLength g := by
      rw [hgc]
      exact FreeProductCyclic.length_le_sylLength_conj hij u c
    omega

/-- The cyclic half restricts out of the full bound: a cyclically reduced word is
nontrivial. -/
theorem cyclicLengthBound_of_lengthBound {R : Set (Word G)}
    (h : GreendlingerLengthBound R) : CyclicLengthBound R := by
  intro i j u hij hu
  refine h u.prod ?_ hu
  intro h1
  exact FreeProductCyclic.pow_ne_one_of_ne hij u 0
    (by rw [zero_add, pow_one]; exact h1)

/-- The short half restricts out of the full bound: a relator of two syllables or
more cannot be less than twice a single syllable. -/
theorem noShortRelation_of_lengthBound {R : Set (Word G)}
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (h : GreendlingerLengthBound R) :
    NoShortRelation R := by
  intro g hg hshort
  by_contra hne
  obtain ⟨r, hr, hlt⟩ := h g hne hg
  have h2 := two_le_wlen (hcyc r hr)
  omega

/-- **The length bound is exactly its two halves.**  Both directions proved, so a
prover may attack either half in isolation and neither is a strengthening. -/
theorem greendlingerLengthBound_iff {R : Set (Word G)}
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) :
    GreendlingerLengthBound R ↔ CyclicLengthBound R ∧ NoShortRelation R :=
  ⟨fun h => ⟨cyclicLengthBound_of_lengthBound h,
      noShortRelation_of_lengthBound hcyc h⟩,
    fun h => greendlingerLengthBound_of_cyclic h.1 h.2⟩

/-- **The embedding clause needs only the short half.**  A difference of two
factor elements dying in the quotient is an element of one syllable in the
relator subgroup; `NoShortRelation` makes it trivial, and `CoprodI.of` is
injective.  No length bound, no metric condition, no cyclic reducedness. -/
theorem factorMap_injective_of_noShortRelation {R : Set (Word G)}
    (h : NoShortRelation R) (i : ι) :
    Function.Injective (factorMap (relatorSubgroup R) i) := by
  intro x y hxy
  have hmem : CoprodI.of (x * y⁻¹) ∈ relatorSubgroup R := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : factorMap (relatorSubgroup R) i (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact h1
  have hone : CoprodI.of (x * y⁻¹) = 1 :=
    h _ hmem (FreeProductCyclic.sylLength_of_le_one _)
  have h2 : x * y⁻¹ = 1 := CoprodI.of_injective i (by rw [hone, map_one])
  exact mul_inv_eq_one.mp h2

/-- The degenerate family meets the cyclic half outright. -/
theorem cyclicLengthBound_of_eq_bot {R : Set (Word G)}
    (hR : relatorSubgroup R = ⊥) : CyclicLengthBound R := by
  intro i j u hij hu
  exfalso
  rw [hR, Subgroup.mem_bot] at hu
  exact FreeProductCyclic.pow_ne_one_of_ne hij u 0
    (by rw [zero_add, pow_one]; exact hu)

/-- The degenerate family meets the short half outright. -/
theorem noShortRelation_of_eq_bot {R : Set (Word G)}
    (hR : relatorSubgroup R = ⊥) : NoShortRelation R := by
  intro g hg _
  rw [hR, Subgroup.mem_bot] at hg
  exact hg

/-! ## 4.  The fragment slack -/

/-- **The fragment slack, as one inequality.**  A whole-syllable piece of `p`
syllables extends to a classical Lyndon--Schupp piece of at most `p + 1` — the
extra syllable being a *fragment* of the next one, which is a piece as soon as
the two relators' next syllables lie in the same factor, since then every element
of that factor is a common prefix fragment.  So a family that is `C'(lam)` for
whole-syllable pieces is `C'(lam + 1/|r|)` classically, and this predicate is
exactly the demand that the corrected constant still clear `1/6`:

    lam · |r| + 1 ≤ (1/6) · |r|   for every relator `r`.

Note what it forbids: `lam = 1/6` satisfies it for *no* relator length, so no
length hypothesis can rescue the constant `1/6` at whole-syllable pieces.  The
constant must drop strictly below `1/6` first, and the relators must then be at
least `1 / (1/6 - lam)` syllables long. -/
def FragmentSlack (R : Set (Word G)) (lam : ℚ) : Prop :=
  ∀ r ∈ R, lam * (wlen r : ℚ) + 1 ≤ (1 / 6) * (wlen r : ℚ)

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- The concrete pair this file's corollaries use: `lam ≤ 1/7` and relators of at
least `42` syllables, since `1/6 - 1/7 = 1/42`.  Any other pair with `lam < 1/6`
and `wlen r ≥ 1 / (1/6 - lam)` does as well — `24` syllables at `1/8`, `12` at
`1/12` — and this lemma is the only place the numbers appear. -/
theorem fragmentSlack_of_le_seventh {R : Set (Word G)} {lam : ℚ}
    (hlam : lam ≤ 1 / 7) (hlong : ∀ r ∈ R, 42 ≤ wlen r) :
    FragmentSlack R lam := by
  intro r hr
  have hw : (42 : ℚ) ≤ (wlen r : ℚ) := by exact_mod_cast hlong r hr
  have h1 : lam * (wlen r : ℚ) ≤ (1 / 7) * (wlen r : ℚ) :=
    mul_le_mul_of_nonneg_right hlam (by linarith)
  linarith

/-! ## 5.  The two open leaves, named

Both are the same van Kampen count the free-group gate
`SmallCancellationRouter.GreendlingerGate` is waiting on, read over syllables
instead of letters, and each is stated at the weakest form this file could cut it
down to.  They are predicates, not hypothesis packages, so every theorem that
spends one carries it visibly in its binder list. -/

/-- **OPEN LEAF.**  The relative Greendlinger lemma, at the length form.

A symmetrized `C'(lam)` family of cyclically reduced relators, with enough
fragment slack to clear the classical `1/6`, makes every nontrivial element of
the relator subgroup longer than half of some relator.

The proof to write is Lyndon--Schupp Ch. V §§9--11 over syllables: a reduced van
Kampen diagram over the free product whose boundary is the normal form, the
curvature count on its interior, and the boundary-layer estimate that `C'(1/6)`
turns into "more than half".  `FragmentSlack` is what licenses the step from the
in-repo whole-syllable pieces to the classical fragment pieces the diagram
argument counts, and it is the only place the two conventions differ.

Three reductions are already applied to it, so a diagram argument may assume all
three: `greendlingerLengthBound_iff` splits it into the cyclic half and the short
half, either attackable alone; `cyclicLengthBound_at_conj` closes the cyclic half
for a single conjugate outright, with the sharp constant `1`, so only expressions
with two or more conjugate factors are left; and the subword form is not needed,
`relativeGreendlingerLeaf_of_subword` recording that it would do. -/
def RelativeGreendlingerLeaf (R : Set (Word G)) (lam : ℚ) : Prop :=
  Symmetrized R → (∀ r ∈ R, IsCyclicallyReduced r) → FragmentSlack R lam →
    MetricSmallCancellation R lam → GreendlingerLengthBound R

/-- **OPEN LEAF.**  The relative torsion classification, at root closure.

A cyclically reduced word one of whose positive powers lies in the relator
subgroup is itself in the relator subgroup.  The proof to write is the annular
companion of the previous one — Greendlinger for a diagram whose two boundary
components read `uⁿ` and the empty word — and it is where `NoProperPower` is
spent: without it the conclusion is false, witnessed by `(xy)^7`, whose seventh
root is a torsion element of the quotient belonging to no conjugate of a factor.

Two reductions are already applied: the quotient is gone
(`cyclicTorsionIntoFactors_of_rootClosed`, with
`rootClosed_of_cyclicTorsionIntoFactors` the converse over torsion-free factors),
and the exponent may be assumed prime (`cyclicPowerRootClosed_iff_prime`). -/
def RelativeTorsionLeaf (R : Set (Word G)) (lam : ℚ) : Prop :=
  Symmetrized R → (∀ r ∈ R, IsCyclicallyReduced r) → FragmentSlack R lam →
    MetricSmallCancellation R lam → NoProperPower R → CyclicPowerRootClosed R

/-- **The subword form would do.**  A proof of the classical Greendlinger
conclusion — a contiguous block making up more than half of a relator — supplies
the leaf, since the length form is what it implies and all this file consumes. -/
theorem relativeGreendlingerLeaf_of_subword {R : Set (Word G)} {lam : ℚ}
    (h : Symmetrized R → (∀ r ∈ R, IsCyclicallyReduced r) → FragmentSlack R lam →
      MetricSmallCancellation R lam → GreendlingerConclusion R) :
    RelativeGreendlingerLeaf R lam :=
  fun hsym hcyc hslack hmetric =>
    greendlingerLengthBound_of_conclusion (h hsym hcyc hslack hmetric)

/-- **The two halves would do.** -/
theorem relativeGreendlingerLeaf_of_split {R : Set (Word G)} {lam : ℚ}
    (hcy : Symmetrized R → (∀ r ∈ R, IsCyclicallyReduced r) → FragmentSlack R lam →
      MetricSmallCancellation R lam → CyclicLengthBound R)
    (hsh : Symmetrized R → (∀ r ∈ R, IsCyclicallyReduced r) → FragmentSlack R lam →
      MetricSmallCancellation R lam → NoShortRelation R) :
    RelativeGreendlingerLeaf R lam :=
  fun hsym hcyc hslack hmetric =>
    greendlingerLengthBound_of_cyclic (hcy hsym hcyc hslack hmetric)
      (hsh hsym hcyc hslack hmetric)

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- **The prime case would do.** -/
theorem relativeTorsionLeaf_of_prime {R : Set (Word G)} {lam : ℚ}
    (h : Symmetrized R → (∀ r ∈ R, IsCyclicallyReduced r) → FragmentSlack R lam →
      MetricSmallCancellation R lam → NoProperPower R → CyclicPrimeRootClosed R) :
    RelativeTorsionLeaf R lam :=
  fun hsym hcyc hslack hmetric hnpp =>
    cyclicPowerRootClosed_of_prime (h hsym hcyc hslack hmetric hnpp)

/-- **Neither leaf is empty.**  The empty relator family satisfies the length
leaf outright. -/
theorem relativeGreendlingerLeaf_empty {lam : ℚ} :
    RelativeGreendlingerLeaf (∅ : Set (Word G)) lam :=
  fun _ _ _ _ => greendlingerLengthBound_empty

/-- The empty relator family satisfies the torsion leaf outright. -/
theorem relativeTorsionLeaf_empty {lam : ℚ} :
    RelativeTorsionLeaf (∅ : Set (Word G)) lam :=
  fun _ _ _ _ _ => cyclicPowerRootClosed_of_eq_bot relatorSubgroup_empty

/-! ## 6.  The compositions, and the single consumption point -/

/-- The length bound, from the leaf. -/
theorem greendlingerLengthBound_of_slack {R : Set (Word G)} {lam : ℚ}
    (hleaf : RelativeGreendlingerLeaf R lam) (hsym : Symmetrized R)
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (hslack : FragmentSlack R lam)
    (hmetric : MetricSmallCancellation R lam) :
    GreendlingerLengthBound R :=
  hleaf hsym hcyc hslack hmetric

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- The torsion classification on cyclically reduced words, from the leaf. -/
theorem cyclicTorsionIntoFactors_of_slack {R : Set (Word G)} {lam : ℚ}
    (hleaf : RelativeTorsionLeaf R lam) (hsym : Symmetrized R)
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (hslack : FragmentSlack R lam)
    (hmetric : MetricSmallCancellation R lam) (hnpp : NoProperPower R) :
    CyclicTorsionIntoFactors R :=
  cyclicTorsionIntoFactors_of_rootClosed (hleaf hsym hcyc hslack hmetric hnpp)

/-- The torsion classification over the whole quotient, from the leaf. -/
theorem torsionIntoFactors_of_slack {R : Set (Word G)} {lam : ℚ}
    (hleaf : RelativeTorsionLeaf R lam) (hsym : Symmetrized R)
    (hcyc : ∀ r ∈ R, IsCyclicallyReduced r) (hslack : FragmentSlack R lam)
    (hmetric : MetricSmallCancellation R lam) (hnpp : NoProperPower R) :
    TorsionIntoFactors (relatorSubgroup R) :=
  torsionIntoFactors_of_cyclicTorsionIntoFactors
    (cyclicTorsionIntoFactors_of_slack hleaf hsym hcyc hslack hmetric hnpp)

/-- **The consumption point.**

A symmetrized family of long cyclically reduced relators, no one of them a proper
power, satisfying the metric condition, over torsion-free factors, delivers the
entire conclusion list of the relative small-cancellation theorem: the
Greendlinger length bound, the torsion classification, the embedding clause for
*every* factor — in particular the peripheral one — and torsion-freeness of the
quotient.

The two leaves are spent here, once each, and they stand in the binder list. -/
theorem osin_conclusion_of_slack {R : Set (Word G)} {lam : ℚ}
    (hleafG : RelativeGreendlingerLeaf R lam) (hleafT : RelativeTorsionLeaf R lam)
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hslack : FragmentSlack R lam) (hmetric : MetricSmallCancellation R lam)
    (hnpp : NoProperPower R) (hfree : ∀ i, IsPowerTorsionFree (G i)) :
    GreendlingerLengthBound R ∧
      TorsionIntoFactors (relatorSubgroup R) ∧
      (∀ i, Function.Injective (factorMap (relatorSubgroup R) i)) ∧
      IsPowerTorsionFree (CoprodI G ⧸ relatorSubgroup R) := by
  have hlen : GreendlingerLengthBound R :=
    greendlingerLengthBound_of_slack hleafG hsym hcyc hslack hmetric
  have htor : TorsionIntoFactors (relatorSubgroup R) :=
    torsionIntoFactors_of_slack hleafT hsym hcyc hslack hmetric hnpp
  have hinj : ∀ i, Function.Injective (factorMap (relatorSubgroup R) i) :=
    factorMap_injective_of_cyclicallyReduced hlen hcyc
  exact ⟨hlen, htor, hinj,
    isPowerTorsionFree_of_torsionIntoFactors htor hinj hfree⟩

/-- The consumption point at the concrete pair `(1/7, 42)`. -/
theorem osin_conclusion_of_metric {R : Set (Word G)}
    (hleafG : RelativeGreendlingerLeaf R (1 / 7))
    (hleafT : RelativeTorsionLeaf R (1 / 7))
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hlong : ∀ r ∈ R, 42 ≤ wlen r)
    (hmetric : MetricSmallCancellation R (1 / 7)) (hnpp : NoProperPower R)
    (hfree : ∀ i, IsPowerTorsionFree (G i)) :
    GreendlingerLengthBound R ∧
      TorsionIntoFactors (relatorSubgroup R) ∧
      (∀ i, Function.Injective (factorMap (relatorSubgroup R) i)) ∧
      IsPowerTorsionFree (CoprodI G ⧸ relatorSubgroup R) :=
  osin_conclusion_of_slack hleafG hleafT hsym hcyc
    (fragmentSlack_of_le_seventh le_rfl hlong) hmetric hnpp hfree

/-- **Nothing above is vacuous, and the degenerate case spends no leaf.**  The
empty family meets every design hypothesis and both leaves outright, and the
conclusion list is then the statement that a free product of torsion-free groups
contains each factor and is torsion-free. -/
theorem osin_conclusion_of_metric_empty (hfree : ∀ i, IsPowerTorsionFree (G i)) :
    GreendlingerLengthBound (∅ : Set (Word G)) ∧
      TorsionIntoFactors (relatorSubgroup (∅ : Set (Word G))) ∧
      (∀ i, Function.Injective
        (factorMap (relatorSubgroup (∅ : Set (Word G))) i)) ∧
      IsPowerTorsionFree (CoprodI G ⧸ relatorSubgroup (∅ : Set (Word G))) := by
  have hlen : GreendlingerLengthBound (∅ : Set (Word G)) :=
    greendlingerLengthBound_empty
  have htor : TorsionIntoFactors (relatorSubgroup (∅ : Set (Word G))) :=
    torsionIntoFactors_of_eq_bot relatorSubgroup_empty
  have hinj : ∀ i, Function.Injective
      (factorMap (relatorSubgroup (∅ : Set (Word G))) i) :=
    factorMap_injective_of_cyclicallyReduced hlen (by simp)
  exact ⟨hlen, htor, hinj,
    isPowerTorsionFree_of_torsionIntoFactors htor hinj hfree⟩

end Transfer

end GreendlingerRelativeTransfer
end GroupApproximation
