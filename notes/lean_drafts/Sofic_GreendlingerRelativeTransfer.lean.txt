import GroupApproximation.Sofic.OsinRelativeSmallCancellation
import Mathlib.Data.List.Rotate

/-!
# The relative transfer: from the metric condition to the two named predicates

`Sofic.OsinRelativeSmallCancellation` proves the consequence layer of Osin's
two clauses over a free product — the peripheral factor stays embedded, the
quotient stays torsion-free — conditional on two predicates on the relator
family, `GreendlingerLengthBound` and `TorsionIntoFactors`.  This file is the
transfer that feeds them: it fixes the hypotheses under which the metric
small-cancellation condition delivers both, isolates what is actually open,
and assembles the single theorem the router construction consumes.

## The consumption point

`osin_conclusion_of_metric` — one theorem, four conclusions: the length bound,
the torsion classification, the embedding clause for *every* factor, and
torsion-freeness of the quotient.  A caller supplying a relator family and its
design certificates gets the whole conclusion list of the relative
small-cancellation theorem with no further plumbing.

## What is open, and what is not

Open, and marked as a hole in the source:

* `greendlingerConclusion_of_metric` — the relative Greendlinger lemma.
* `cyclicTorsionIntoFactors_of_metric` — the relative torsion classification,
  already reduced to cyclically reduced words (see below).

Everything else here is proved:

* `torsionIntoFactors_of_cyclicTorsionIntoFactors` — **the torsion clause
  reduces to the cyclically reduced case.**  Cyclic reduction splits an
  arbitrary quotient element into three kinds; two of them settle themselves
  (the identity, and a conjugate of a syllable, which is literally the
  conclusion), so the only case a diagram argument ever has to see is a
  cyclically reduced word.  This is the whole of the ∀-over-the-quotient
  quantifier, discharged.
* `greendlingerLengthBound_of_metric`, `torsionIntoFactors_of_metric`,
  `osin_conclusion_of_metric` — the compositions, spending the two holes once
  each.
* `noProperPower_of_prime_wlen` — **a designable criterion for the
  no-proper-power hypothesis.**  A cyclically reduced relator whose syllable
  length is prime is not a proper power, because a proper power's cyclically
  reduced form has length `k · |u|` with both factors at least two, and
  syllable length of the cyclically reduced form is a conjugacy invariant
  (`FreeProductCyclic.length_eq_of_conj`).  So the hypothesis is checkable by
  counting syllables, and W3's relator design can meet it by construction.

## Three hypotheses that are not decoration

The implication as stated in the docstring of `OsinRelativeSmallCancellation`
— `MetricSmallCancellation R (1/6) → GreendlingerLengthBound R` and
`→ TorsionIntoFactors (relatorSubgroup R)` — is false without three further
hypotheses, and each has a witness.

* **Symmetrization** (`Symmetrized`).  `IsPiece R` compares *distinct members
  of `R`*, so a one-element family has no pieces at all and satisfies
  `MetricSmallCancellation R lam` vacuously for every `lam`, while Dehn's
  algorithm needs every rotation and every formal inverse of a relator to be
  available as a competing occurrence.  The free-group side of the same
  program takes this route explicitly: `SmallCancellationRouter` measures
  pieces in `symmetrization R` and never in `R`.  Here symmetrization is a
  hypothesis on `R` rather than a closure operator, because rotating a
  `Word G` means rebuilding it letter by letter, and the router's relator
  family will be presented symmetrized already.

* **No relator is a proper power** (`NoProperPower`).  `C'(1/6)` does not
  imply a torsion-free quotient, over a free product or over a free group.
  Take `G₀ = G₁ = ℤ` with generators `x, y` and the symmetrized family of
  `(xy)^7`: its rotations by an even number of syllables are the word itself,
  the odd rotations begin in the other factor, and the inverses begin with
  inverse letters, so *no two distinct members share even one syllable of
  prefix* — the family is `C'(lam)` for every positive `lam`, vacuously — and
  the image of `xy` in the quotient has order `7`.  Since the factors are
  torsion-free and (by the embedding clause) stay embedded, that element is
  not conjugate to the image of any factor element, so `TorsionIntoFactors`
  fails outright.  This is Lyndon--Schupp Ch. V, Thm 10.1 read backwards: in
  a `C'(1/6)` group the torsion is *exactly* the conjugates of powers of the
  roots of relators, and it is empty precisely when no relator is a proper
  power.

* **Long relators, and `1/7` rather than `1/6`** (`hlong`, and the constant in
  `hmetric`).  Pieces here are whole syllables: `IsPiece R p` asks for `p` to
  be a prefix of two relators *as syllable lists*.  Over a free product the
  classical piece may also end in a *fragment* of a syllable — `u = u₁u₂` with
  only `u₁` shared — and Lyndon--Schupp count that fragment as a full syllable
  of the piece.  So the classical family of pieces is strictly larger, and the
  in-repo condition is the *weaker* of the two, not the stronger: a
  whole-syllable piece of length `k` extends to a classical piece of length
  `k + 1`, no more, since truncating a classical piece to its complete
  syllables gives a whole-syllable piece.  Hence whole-syllable `C'(lam)`
  gives classical `C'(lam + 1/|r|)`, and

      lam = 1/7  and  |r| ≥ 42   ⟹   lam + 1/|r| ≤ 1/7 + 1/42 = 1/6,

  which is the classical hypothesis with room to spare.  Both numbers are free
  design parameters for a Rips-style relator family — long blocks with
  disjoint ranges are what such a family is made of — so nothing downstream
  pays for the correction.  `FragmentSlack` states the inequality once and
  `fragmentSlack_of_le_seventh` is the only place the two numbers appear, so a
  caller may substitute any pair with `lam < 1/6` and `|r| ≥ 1 / (1/6 - lam)`.
  What *cannot* be substituted is `lam = 1/6` with a length hypothesis: the
  slack inequality fails there for every length, so lowering the constant is
  not optional.  A fragment-aware `IsPiece` would let the constant be `1/6`
  and delete the length hypothesis; that is a refinement of the *definitions*
  in `OsinRelativeSmallCancellation`, not of anything proved here.

  The bare implication has an explicit refutation, found by the router
  construction: over `ℤ * ℤ/3` with generators `e` and `b`, the symmetrized
  family of the two-syllable relator `e·b⁻¹` has pairwise distinct first
  syllables — `e`, `b⁻¹`, `b`, `e⁻¹` — hence no nonempty whole-syllable piece
  at all, so `MetricSmallCancellation R (1/6)` holds vacuously; but `e ≡ b` in
  the quotient forces `of (e³)` into the relator subgroup, an element of
  syllable length one, and the length bound would need a relator shorter than
  two syllables.  The witness spends the torsion of `ℤ/3` and any relator
  length hypothesis kills it, but it is not what the slack inequality is
  guarding against: the slack is needed at every length, because the classical
  count needs classical pieces.

**This module has two open leaves and must not be root-imported until they are
discharged.**  Everything else here is an honest derivation, but the four
consumption points all call a leaf, and an incomplete proof propagates through
a call with no warning at the call site.  `scripts/Audit.lean`'s axiom probe is
the gate of record; green elaboration means the statements typecheck and
compose, not that the results hold.
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

/-- **The family is symmetrized**: every cyclic rotation of a relator, and
every rotation of a relator's formal inverse, is again a relator.

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

/-- **No relator is a proper power.**  Without this the quotient acquires
torsion of its own: see the `(xy)^7` witness in the module docstring. -/
def NoProperPower (R : Set (Word G)) : Prop :=
  ∀ r ∈ R, ∀ (s : CoprodI G) (k : ℕ), 2 ≤ k → r.prod ≠ s ^ k

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
theorem noProperPower_empty : NoProperPower (∅ : Set (Word G)) := by
  intro r hr
  simp at hr

/-- **A prime syllable count rules out proper powers.**

A proper power `s ^ k` is conjugate to `u ^ k` for a cyclically reduced `u`,
and `|u ^ k| = k · |u|` on the nose, so the cyclically reduced length of a
proper power factors with both factors at least two.  Syllable length of a
cyclically reduced form is a conjugacy invariant, so that factorization is a
factorization of `wlen r` — impossible for a prime.

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

/-! ## 2.  The torsion clause, reduced to cyclically reduced words -/

/-- **Osin's torsion clause, restricted to cyclically reduced words.**  The
same disjunction as `TorsionIntoFactors`, asked only of the image of a word
whose first and last syllables lie in different factors.

The disjunction is not "the word is in the relator subgroup": over a free
product with torsion in the factors it must not be.  With `G₀ = ℤ/7 = ⟨x⟩`,
`G₁ = ℤ = ⟨y⟩` and the symmetrized family of the two-syllable relator `xy`,
the cyclically reduced word `x y²` has image `y = x⁻¹` in the quotient, whose
seventh power is trivial while the word itself is not in the relator subgroup.
It *is* conjugate to the image of a factor element, which is exactly what the
second disjunct says. -/
def CyclicTorsionIntoFactors (R : Set (Word G)) : Prop :=
  ∀ (i j : ι) (u : NeWord G i j), i ≠ j → ∀ n : ℕ, 0 < n →
    u.prod ^ n ∈ relatorSubgroup R →
      QuotientGroup.mk' (relatorSubgroup R) u.prod = 1 ∨
        ∃ (p : ι) (x : G p) (d : CoprodI G ⧸ relatorSubgroup R),
          QuotientGroup.mk' (relatorSubgroup R) u.prod
            = d * factorMap (relatorSubgroup R) p x * d⁻¹

/-- **The quantifier over the quotient, discharged.**  Cyclic reduction sorts
every element of the free product into three kinds; the identity and the
conjugates of a single syllable *are* the conclusion, and the cyclically
reduced case is passed on.  So a proof of the torsion clause never has to look
at a word that is not cyclically reduced. -/
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

/-- **Root closure on cyclically reduced words**: a cyclically reduced word
with a positive power in the relator subgroup is itself in the relator
subgroup.

Over torsion-free factors this is an equivalent form of
`CyclicTorsionIntoFactors` (both directions below), and it is the form to aim
a proof at: it mentions the quotient nowhere.  It is *not* equivalent in
general — the `ℤ/7` witness in the docstring of `CyclicTorsionIntoFactors`
satisfies that predicate and refutes this one — so the equivalence is spent
against the torsion-freeness of the factors, exactly once. -/
def CyclicPowerRootClosed (R : Set (Word G)) : Prop :=
  ∀ (i j : ι) (u : NeWord G i j), i ≠ j → ∀ n : ℕ, 0 < n →
    u.prod ^ n ∈ relatorSubgroup R → u.prod ∈ relatorSubgroup R

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- Root closure is the stronger predicate, unconditionally. -/
theorem cyclicTorsionIntoFactors_of_rootClosed {R : Set (Word G)}
    (h : CyclicPowerRootClosed R) : CyclicTorsionIntoFactors R := by
  intro i j u hij n hn hu
  left
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact h i j u hij n hn hu

/-- **The converse, over torsion-free factors.**  The second disjunct of
`CyclicTorsionIntoFactors` names a factor element whose `n`-th power dies in
the quotient; the embedding clause carries that back to the factor, where
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

/-! ## 3.  The two open leaves

Both are the same van Kampen count the free-group gate
`SmallCancellationRouter.GreendlingerGate` is waiting on, read over syllables
instead of letters.  They are stated here so that everything downstream is
written against these names, and so that discharging them is a local edit. -/

/-- **The fragment slack, as one inequality.**  A whole-syllable piece of `p`
syllables extends to a classical Lyndon--Schupp piece of at most `p + 1` — the
extra syllable being a *fragment* of the next one, which is a piece as soon as
the two relators' next syllables lie in the same factor, since then every
element of that factor is a common prefix fragment.  So a family that is
`C'(lam)` for whole-syllable pieces is `C'(lam + 1/|r|)` classically, and this
predicate is exactly the demand that the corrected constant still clear `1/6`:

    lam · |r| + 1 ≤ (1/6) · |r|   for every relator `r`.

Note what it forbids: `lam = 1/6` satisfies it for *no* relator length, so no
length hypothesis can rescue the constant `1/6` at whole-syllable pieces.  The
constant must drop strictly below `1/6` first, and the relators must then be at
least `1 / (1/6 - lam)` syllables long. -/
def FragmentSlack (R : Set (Word G)) (lam : ℚ) : Prop :=
  ∀ r ∈ R, lam * (wlen r : ℚ) + 1 ≤ (1 / 6) * (wlen r : ℚ)

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- The concrete pair this file's corollaries use: `lam ≤ 1/7` and relators of
at least `42` syllables, since `1/6 - 1/7 = 1/42`.  Any other pair with
`lam < 1/6` and `wlen r ≥ 1 / (1/6 - lam)` does as well — `24` syllables at
`1/8`, `12` at `1/12` — and this lemma is the only place the numbers appear. -/
theorem fragmentSlack_of_le_seventh {R : Set (Word G)} {lam : ℚ}
    (hlam : lam ≤ 1 / 7) (hlong : ∀ r ∈ R, 42 ≤ wlen r) :
    FragmentSlack R lam := by
  intro r hr
  have hw : (42 : ℚ) ≤ (wlen r : ℚ) := by exact_mod_cast hlong r hr
  have h1 : lam * (wlen r : ℚ) ≤ (1 / 7) * (wlen r : ℚ) :=
    mul_le_mul_of_nonneg_right hlam (by linarith)
  linarith

/-- **OPEN.**  The relative Greendlinger lemma: a symmetrized `C'(lam)` family
of cyclically reduced relators, with enough fragment slack to clear the
classical `1/6`, satisfies the Greendlinger conclusion — a nontrivial element
of the relator subgroup carries, inside its normal form, a contiguous block
making up more than half of some relator read cyclically.

The proof to write is Lyndon--Schupp Ch. V §§9--11 over syllables: a reduced
van Kampen diagram over the free product whose boundary is the normal form,
the curvature count on its interior, and the boundary-layer estimate that
`C'(1/6)` turns into "more than half".  `FragmentSlack` is what licenses the
step from the in-repo whole-syllable pieces to the classical fragment pieces
the diagram argument counts, and it is the only place the two conventions
differ.

The one-conjugate case is not open: `OsinSmallCancellation.wlen_le_sylLength_conj`
proves it outright, with the sharp constant `1` in place of `1/2`.  What the
count adds is that the cancellations between *different* conjugates cannot all
be large. -/
theorem greendlingerConclusion_of_slack {R : Set (Word G)} {lam : ℚ}
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hslack : FragmentSlack R lam)
    (hmetric : MetricSmallCancellation R lam) :
    GreendlingerConclusion R := by
  sorry

/-- **OPEN.**  The relative torsion classification, in the reduced form
`torsionIntoFactors_of_cyclicTorsionIntoFactors` leaves: a cyclically reduced
word one of whose positive powers lies in the relator subgroup is itself in
the relator subgroup, or its image is conjugate to the image of an element of
a factor.

The proof to write is the annular companion of the previous one — Greendlinger
for a diagram whose two boundary components read `uⁿ` and the empty word —
and it is where `NoProperPower` is spent: without it the conclusion is false,
witnessed by `(xy)^7`, whose seventh root is a torsion element of the quotient
belonging to no conjugate of a factor. -/
theorem cyclicTorsionIntoFactors_of_slack {R : Set (Word G)} {lam : ℚ}
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hslack : FragmentSlack R lam)
    (hmetric : MetricSmallCancellation R lam) (hnpp : NoProperPower R) :
    CyclicTorsionIntoFactors R := by
  sorry

/-- The Greendlinger lemma at the concrete pair `(1/7, 42)`. -/
theorem greendlingerConclusion_of_metric {R : Set (Word G)}
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hlong : ∀ r ∈ R, 42 ≤ wlen r)
    (hmetric : MetricSmallCancellation R (1 / 7)) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_slack hsym hcyc
    (fragmentSlack_of_le_seventh le_rfl hlong) hmetric

/-- The torsion classification at the concrete pair `(1/7, 42)`. -/
theorem cyclicTorsionIntoFactors_of_metric {R : Set (Word G)}
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hlong : ∀ r ∈ R, 42 ≤ wlen r)
    (hmetric : MetricSmallCancellation R (1 / 7)) (hnpp : NoProperPower R) :
    CyclicTorsionIntoFactors R :=
  cyclicTorsionIntoFactors_of_slack hsym hcyc
    (fragmentSlack_of_le_seventh le_rfl hlong) hmetric hnpp

/-! ## 4.  The compositions, and the single consumption point -/

/-- The length form of the Greendlinger conclusion, which is what the
embedding clause consumes. -/
theorem greendlingerLengthBound_of_metric {R : Set (Word G)}
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hlong : ∀ r ∈ R, 42 ≤ wlen r)
    (hmetric : MetricSmallCancellation R (1 / 7)) :
    GreendlingerLengthBound R :=
  greendlingerLengthBound_of_conclusion
    (greendlingerConclusion_of_metric hsym hcyc hlong hmetric)

/-- The torsion classification over the whole quotient. -/
theorem torsionIntoFactors_of_metric {R : Set (Word G)}
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hlong : ∀ r ∈ R, 42 ≤ wlen r)
    (hmetric : MetricSmallCancellation R (1 / 7)) (hnpp : NoProperPower R) :
    TorsionIntoFactors (relatorSubgroup R) :=
  torsionIntoFactors_of_cyclicTorsionIntoFactors
    (cyclicTorsionIntoFactors_of_metric hsym hcyc hlong hmetric hnpp)

/-- **The consumption point.**

A symmetrized family of long cyclically reduced relators, no one of them a
proper power, satisfying the metric condition, over torsion-free factors,
delivers the entire conclusion list of the relative small-cancellation
theorem: the Greendlinger length bound, the torsion classification, the
embedding clause for *every* factor — in particular the peripheral one — and
torsion-freeness of the quotient.

The two open leaves are spent here, once each, and nothing downstream of this
theorem mentions them. -/
theorem osin_conclusion_of_slack {R : Set (Word G)} {lam : ℚ}
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hslack : FragmentSlack R lam) (hmetric : MetricSmallCancellation R lam)
    (hnpp : NoProperPower R) (hfree : ∀ i, IsPowerTorsionFree (G i)) :
    GreendlingerLengthBound R ∧
      TorsionIntoFactors (relatorSubgroup R) ∧
      (∀ i, Function.Injective (factorMap (relatorSubgroup R) i)) ∧
      IsPowerTorsionFree (CoprodI G ⧸ relatorSubgroup R) := by
  have hlen : GreendlingerLengthBound R :=
    greendlingerLengthBound_of_conclusion
      (greendlingerConclusion_of_slack hsym hcyc hslack hmetric)
  have htor : TorsionIntoFactors (relatorSubgroup R) :=
    torsionIntoFactors_of_cyclicTorsionIntoFactors
      (cyclicTorsionIntoFactors_of_slack hsym hcyc hslack hmetric hnpp)
  have hinj : ∀ i, Function.Injective (factorMap (relatorSubgroup R) i) :=
    factorMap_injective_of_cyclicallyReduced hlen hcyc
  exact ⟨hlen, htor, hinj,
    isPowerTorsionFree_of_torsionIntoFactors htor hinj hfree⟩

/-- The consumption point at the concrete pair `(1/7, 42)`. -/
theorem osin_conclusion_of_metric {R : Set (Word G)}
    (hsym : Symmetrized R) (hcyc : ∀ r ∈ R, IsCyclicallyReduced r)
    (hlong : ∀ r ∈ R, 42 ≤ wlen r)
    (hmetric : MetricSmallCancellation R (1 / 7)) (hnpp : NoProperPower R)
    (hfree : ∀ i, IsPowerTorsionFree (G i)) :
    GreendlingerLengthBound R ∧
      TorsionIntoFactors (relatorSubgroup R) ∧
      (∀ i, Function.Injective (factorMap (relatorSubgroup R) i)) ∧
      IsPowerTorsionFree (CoprodI G ⧸ relatorSubgroup R) :=
  osin_conclusion_of_slack hsym hcyc (fragmentSlack_of_le_seventh le_rfl hlong)
    hmetric hnpp hfree

/-- **Nothing above is vacuous.**  The empty family meets every design
hypothesis, and the conclusion list is then the statement that a free product
of torsion-free groups contains each factor and is torsion-free. -/
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
