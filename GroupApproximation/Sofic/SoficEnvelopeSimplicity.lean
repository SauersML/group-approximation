import GroupApproximation.Sofic.SoficEnvelopeExistence
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Units
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign

/-!
# Move 2 of Elek--Szabó: simplicity of the universal sofic group

`GroupApproximation.Sofic.SoficEnvelopeExistence` reduces the manuscript's
paragraph *A simple sofic envelope* to one missing input, which its docstring
names: the metric ultraproduct `UniversalSofic 𝒰 X` of finite symmetric groups
is simple when the model cardinalities diverge along `𝒰`.  This file discharges
everything in that statement except one finite-combinatorial theorem about
alternating groups, and isolates that theorem as a spelled-out premise so that no
declaration here can be mistaken for a proof of it.

## What is proved outright

The ultraproduct half of the argument is proved here with no hypothesis beyond
divergence of the model cardinalities.

* `mk_eq_mk_of_eventually_eq` -- two sequences agreeing on a `𝒰`-large set have
  the same class.  This is the reason the argument can choose exponents by
  ultrafilter limit: a modification on a `𝒰`-small set costs nothing.
* `isNullSeq_of_bounded_support` -- a sequence of permutations with uniformly
  bounded supports is null once the models grow.
* `exists_even_representative` -- every class is represented by a sequence of
  *even* permutations.  This is the step that removes the sign obstruction:
  the sign of a sequence of permutations is not a function of its class, but
  only because a transposition is null, and correcting by one transposition per
  index is exactly a bounded-support modification.
* `exists_ne_one_universalSofic` -- the ultraproduct is nontrivial, witnessed by
  a fixed-point-free permutation in each model of size at least two.
* `exists_pos_support_density_of_diverging` -- the density reduction of
  `SoficEnvelopeExistence`, restated under divergence rather than pointwise
  positivity of the model cardinalities, which is what a sofic approximation
  actually supplies.
* `mk_mem_of_eventually_isBoundedConjProduct` -- the transfer step, and the
  mathematical heart of this file: if a normal subgroup of the ultraproduct
  contains the class of `σ`, and `α i` is a product of at most `K` conjugates of
  `(σ i)^{±1}` for `𝒰`-many `i`, then it contains the class of `α`.  The bound
  `K` must not depend on `i`, and neither may the *exponents*: the ultrafilter
  chooses one exponent per factor position, and the indices where a factor used
  a different exponent form a `𝒰`-small set, which the previous item makes free.

## What is assumed, and where

The remaining input is **bounded normal generation of finite alternating
groups**:

> for every `δ > 0` there are `K` and `M` such that whenever `Ω` is a finite set
> with `|Ω| ≥ M` and `s` is an **even** permutation of `Ω` with
> `|supp s| ≥ δ|Ω|`, every even permutation of `Ω` is a product of at most `K`
> conjugates of `s` and `s⁻¹`.

## Why the premise is already at its weakest

Four separate weakenings are built into that sentence, each of them something
the argument below is arranged to give away rather than demand.

* **`s` may be assumed even.**  `isSimpleGroup_universalSofic` does not use the
  representative it is handed; it replaces it by an even one first, using
  `exists_even_representative` on the *source* class as well as the target.  The
  class, and hence membership in the normal subgroup and nontriviality, are
  untouched.  This is what puts the premise on the literature's own turf: the
  Liebeck--Shalev covering bounds are theorems about `Aₙ`, so with `s` even the
  premise is a statement about `Aₙ` and its `Sym(Ω)`-conjugates rather than a
  statement about `Sym(Ω)` that a reader would have to reduce by hand.
* **Only even targets `a` need be reached**, never all of the normal closure of
  `s`.  When `s` is odd its normal closure in `Sym(Ω)` is all of `Sym(Ω)` for
  `|Ω| ≥ 5`, so demanding the normal closure would be strictly more; the even
  half is all `exists_even_representative` ever asks for.
* **The conjugators range over all of `Sym(Ω)`**, not just `Aₙ`, which is the
  easier of the two demands.
* **A size threshold `M` is permitted**, and is in any case unavoidable.

What cannot be given away is the *uniformity* of `K` -- see below.

## What cannot be weakened, and why the obvious weakening fails

`K` may depend on `δ` and on nothing else.  It may not depend on the index `i`,
because `mk_mem_of_eventually_isBoundedConjProduct` assembles one product of a
single fixed length out of the coordinatewise products; a length varying with
`i` has no image in the quotient.  Since the coordinates `α i` of an arbitrary
class are arbitrary even permutations, `K` must work for all of them at once.

The one weakening that looks like it should work is the **approximate** form --
reach `a` only to within normalized Hamming distance `ε` by a product of at most
`K(δ, ε)` conjugates.  It does not suffice, and the reason is worth recording so
that nobody re-attempts it.  Iterating the approximation writes
`a = b₁ b₂ ⋯ b_m r_m` with each `b_j` a product of at most `K` conjugates and
`|r_m| ≤ 2^{-m}`; the residual is killed in the ultraproduct only by letting
`m → ∞` along `𝒰`, which is exactly a number of factors tending to infinity with
the index.  That is the one thing the quotient cannot absorb, and it is why
*bounded* normal generation, rather than plain normal generation, is the real
content of the citation.

That is a theorem of the literature -- the Liebeck--Shalev covering bounds for
alternating groups supply it, and it is the input Elek--Szabó use -- and it is
not proved anywhere in this repository.  It is therefore written out in full, as
a premise `hBNG`, on exactly the two declarations that need it
(`isSimpleGroup_universalSofic` and `exists_countable_simple_sofic_envelope`),
and on nothing else in this file; the one composite in
`GroupApproximation.Sofic.SoficEnvelopeWitness` carries the same premise
verbatim.

The premise is deliberately *not* packaged as a named proposition:
`scripts/Audit.lean` keeps `literatureInputNames` empty on purpose, and a
corpus-defined predicate standing for someone else's theorem is precisely what
that roster exists to catch.  Two names do occur inside `hBNG`, and neither is a
claim: `FiniteModel` is this development's bundling of a finite type with the
counting and equality instances a permutation model needs, and
`IsBoundedConjProduct` is the structural predicate "a product of at most `K`
conjugates of `s` and `s⁻¹`", which is inhabited outright
(`isBoundedConjProduct_one`) and is proved to imply membership in the normal
closure of `s` (`mem_normalClosure_of_isBoundedConjProduct`), so it refines
normal generation rather than replacing it with something weaker.  What `hBNG`
asserts -- the existence of a bound depending only on the density -- is written
as a quantified sentence with no abbreviation hiding any part of it.

The same doctrine has a consequence that must be stated plainly: **no
declaration in this file may ever carry a `\leanverified` badge.**  The
manuscript's paragraph is printed with a citation to Elek--Szabó, and the badge
surface is reserved for results this corpus proves outright.  What this file
buys is that the *rest* of the argument -- everything the citation is used for
after the sentence it appears in -- is machine-checked, and that the remaining
debt is one sentence about finite alternating groups rather than a theorem about
metric ultraproducts.

Note also that `M` is genuinely needed in `hBNG`: for `Ω` of size four and `s`
a product of two disjoint transpositions, `|supp s| = |Ω|` while the normal
closure of `s` is the Klein four-group, which misses every three-cycle.  Any
threshold at or above five removes that obstruction, and divergence of the
model cardinalities makes a threshold free.
-/

namespace GroupApproximation
namespace SoficEnvelopeSimplicity

open Filter SoficEnvelopeExistence

/-! ## Modification on a `𝒰`-small set is free -/

/-- Two sequences of permutations that agree on a `𝒰`-large set of indices have
the same class in the metric ultraproduct.  Their quotient is the identity
`𝒰`-often, hence has Hamming length zero there, hence is null.  No hypothesis on
the models is needed. -/
theorem mk_eq_mk_of_eventually_eq {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel) {u v : ∀ i, Equiv.Perm (X i)}
    (h : ∀ᶠ i in (𝒰 : Filter ι), u i = v i) :
    (QuotientGroup.mk u : UniversalSofic 𝒰 X) = QuotientGroup.mk v := by
  have hnull : u⁻¹ * v ∈ nullSubgroup 𝒰 X := by
    intro ε hε
    filter_upwards [h] with i hi
    have hone : (u⁻¹ * v) i = 1 := by
      show (u i)⁻¹ * v i = 1
      rw [hi, inv_mul_cancel]
    rw [hone, hammingLength_one]
    exact hε
  exact QuotientGroup.eq.mpr hnull

/-- A sequence of permutations whose supports are bounded by one constant is
null as soon as the model cardinalities diverge: its normalized Hamming length
is at most `C / |X i|`. -/
theorem isNullSeq_of_bounded_support {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel)
    (hdiv : ∀ M : ℕ, ∀ᶠ i in (𝒰 : Filter ι), M ≤ Fintype.card (X i))
    (t : ∀ i, Equiv.Perm (X i)) (C : ℕ)
    (ht : ∀ i, (t i).support.card ≤ C) :
    IsNullSeq 𝒰 X t := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt ((C : ℝ) / ε)
  have hCM : (C : ℝ) < ε * (M : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hM
    rwa [mul_comm] at h
  filter_upwards [hdiv M, hdiv 1] with i hi hi1
  have hi0 : 0 < Fintype.card (X i) := lt_of_lt_of_le Nat.zero_lt_one hi1
  have hcpos : (0 : ℝ) < (Fintype.card (X i) : ℝ) := by exact_mod_cast hi0
  have hcard : (M : ℝ) ≤ (Fintype.card (X i) : ℝ) := by exact_mod_cast hi
  have h1 : ((t i).support.card : ℝ) ≤ (C : ℝ) := by exact_mod_cast ht i
  have h2 : ε * (M : ℝ) ≤ ε * (Fintype.card (X i) : ℝ) :=
    mul_le_mul_of_nonneg_left hcard hε.le
  rw [hammingLength_eq_support_div, div_lt_iff₀ hcpos]
  linarith

/-! ## Every class has an even representative

The sign of a sequence of permutations is not a function of its class: a
transposition is null in every diverging ultraproduct.  Read the other way,
that says the parity of a representative can be chosen, and choosing it is what
lets bounded normal generation -- a statement about *even* permutations -- reach
every class. -/

/-- Every permutation of a finite model becomes even after multiplication by a
permutation moving at most two points: by the identity if it is already even,
and otherwise by the transposition exchanging a moved point with its image. -/
theorem exists_small_sign_correction (Y : FiniteModel) (p : Equiv.Perm Y) :
    ∃ t : Equiv.Perm Y, Equiv.Perm.sign (p * t) = 1 ∧ t.support.card ≤ 2 := by
  classical
  by_cases hsign : Equiv.Perm.sign p = 1
  · refine ⟨1, ?_, ?_⟩
    · rw [mul_one]
      exact hsign
    · rw [Equiv.Perm.support_one, Finset.card_empty]
      exact Nat.zero_le 2
  · have hneg : Equiv.Perm.sign p = -1 :=
      (Int.units_eq_one_or (Equiv.Perm.sign p)).resolve_left hsign
    have hp1 : p ≠ 1 := by
      intro hcon
      exact hsign (by rw [hcon, Equiv.Perm.sign_one])
    have hne : p.support ≠ ∅ := fun hc =>
      hp1 (Equiv.Perm.support_eq_empty_iff.mp hc)
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hmove : a ≠ p a := (Equiv.Perm.mem_support.mp ha).symm
    refine ⟨Equiv.swap a (p a), ?_, ?_⟩
    · rw [Equiv.Perm.sign_mul, hneg, Equiv.Perm.sign_swap hmove, neg_mul_neg,
        one_mul]
    · exact le_of_eq (Equiv.Perm.card_support_swap hmove)

/-- **Every class is represented by even permutations.**  Correcting each
coordinate by at most one transposition changes the sequence by a
bounded-support amount, which the divergence of the models makes null. -/
theorem exists_even_representative {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel)
    (hdiv : ∀ M : ℕ, ∀ᶠ i in (𝒰 : Filter ι), M ≤ Fintype.card (X i))
    (σ : ∀ i, Equiv.Perm (X i)) :
    ∃ α : ∀ i, Equiv.Perm (X i), (∀ i, Equiv.Perm.sign (α i) = 1) ∧
      (QuotientGroup.mk α : UniversalSofic 𝒰 X) = QuotientGroup.mk σ := by
  classical
  choose t ht hts using fun i => exists_small_sign_correction (X i) (σ i)
  refine ⟨σ * t, fun i => ht i, ?_⟩
  have hnull : t ∈ nullSubgroup 𝒰 X :=
    isNullSeq_of_bounded_support 𝒰 X hdiv t 2 hts
  have hmk : (QuotientGroup.mk t : UniversalSofic 𝒰 X) = 1 :=
    (QuotientGroup.eq_one_iff t).mpr hnull
  rw [QuotientGroup.mk_mul, hmk, mul_one]

/-! ## Nontriviality of the ultraproduct

A simple group is by definition nontrivial, and for the ultraproduct that is a
genuine assertion: the null subgroup is large.  A fixed-point-free permutation
has normalized Hamming length one, which no null sequence can match. -/

/-- A finite model with at least two points carries a permutation with full
support: transport the cyclic rotation of `Fin (card Y)` along a counting
bijection. -/
theorem exists_support_eq_univ (Y : FiniteModel) (hY : 2 ≤ Fintype.card Y) :
    ∃ p : Equiv.Perm Y, p.support = Finset.univ := by
  classical
  refine ⟨(Fintype.equivFin Y).trans
    ((finRotate (Fintype.card Y)).trans (Fintype.equivFin Y).symm), ?_⟩
  rw [Finset.eq_univ_iff_forall]
  intro y
  rw [Equiv.Perm.mem_support]
  intro hfix
  -- `Equiv.trans` composes definitionally, so the fixed-point equation reads
  -- off directly after transporting back along the counting bijection.
  have hfix' : (Fintype.equivFin Y).symm
      (finRotate (Fintype.card Y) (Fintype.equivFin Y y)) = y := hfix
  have hy : finRotate (Fintype.card Y) (Fintype.equivFin Y y)
      = Fintype.equivFin Y y :=
    calc finRotate (Fintype.card Y) (Fintype.equivFin Y y)
        = Fintype.equivFin Y ((Fintype.equivFin Y).symm
            (finRotate (Fintype.card Y) (Fintype.equivFin Y y))) :=
          (Equiv.apply_symm_apply _ _).symm
      _ = Fintype.equivFin Y y := by rw [hfix']
  have hmem : Fintype.equivFin Y y ∈ (finRotate (Fintype.card Y)).support := by
    rw [support_finRotate_of_le hY]
    exact Finset.mem_univ _
  exact (Equiv.Perm.mem_support.mp hmem) hy

/-- **The ultraproduct is nontrivial.**  The class of a sequence of
fixed-point-free permutations has normalized Hamming length one at every index
where the model has at least two points, so it is not null. -/
theorem exists_ne_one_universalSofic {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel)
    (hdiv : ∀ M : ℕ, ∀ᶠ i in (𝒰 : Filter ι), M ≤ Fintype.card (X i)) :
    ∃ z : UniversalSofic 𝒰 X, z ≠ 1 := by
  classical
  have hex : ∀ i, ∃ p : Equiv.Perm (X i),
      2 ≤ Fintype.card (X i) → p.support = Finset.univ := by
    intro i
    by_cases h : 2 ≤ Fintype.card (X i)
    · obtain ⟨p, hp⟩ := exists_support_eq_univ (X i) h
      exact ⟨p, fun _ => hp⟩
    · exact ⟨1, fun hc => absurd hc h⟩
  choose p hp using hex
  refine ⟨QuotientGroup.mk p, ?_⟩
  intro hone
  have hnull : p ∈ nullSubgroup 𝒰 X := (QuotientGroup.eq_one_iff p).mp hone
  have hsmall := hnull (1 / 2) (by norm_num)
  have hbig : ∀ᶠ i in (𝒰 : Filter ι), (1 : ℝ) ≤ hammingLength (X i) (p i) := by
    filter_upwards [hdiv 2] with i hi
    have hi0 : 0 < Fintype.card (X i) := by omega
    have hcpos : (0 : ℝ) < (Fintype.card (X i) : ℝ) := by exact_mod_cast hi0
    rw [hammingLength_eq_support_div, hp i hi, Finset.card_univ]
    exact le_of_eq (div_self hcpos.ne').symm
  obtain ⟨i, h1, h2⟩ := (hbig.and hsmall).exists
  linarith

/-- The support-density reduction of `SoficEnvelopeExistence`, restated under
divergence of the model cardinalities rather than pointwise positivity.  This is
the form a sofic approximation supplies, and positivity is only ever used
`𝒰`-often inside the proof. -/
theorem exists_pos_support_density_of_diverging {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel)
    (hdiv : ∀ M : ℕ, ∀ᶠ i in (𝒰 : Filter ι), M ≤ Fintype.card (X i))
    (σ : ∀ i, Equiv.Perm (X i))
    (hσ : (QuotientGroup.mk σ : UniversalSofic 𝒰 X) ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in (𝒰 : Filter ι),
      δ * (Fintype.card (X i) : ℝ) ≤ ((σ i).support.card : ℝ) := by
  obtain ⟨δ, hδ, hev⟩ := exists_pos_hammingLength_of_mk_ne_one 𝒰 X σ hσ
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hev, hdiv 1] with i hi hi1
  rw [hammingLength_eq_support_div] at hi
  have hi0 : 0 < Fintype.card (X i) := lt_of_lt_of_le Nat.zero_lt_one hi1
  have hc : (0 : ℝ) < (Fintype.card (X i) : ℝ) := by exact_mod_cast hi0
  have hmul := mul_le_mul_of_nonneg_right hi hc.le
  calc δ * (Fintype.card (X i) : ℝ)
      ≤ ((σ i).support.card : ℝ) / (Fintype.card (X i) : ℝ) *
          (Fintype.card (X i) : ℝ) := hmul
    _ = ((σ i).support.card : ℝ) := div_mul_cancel₀ _ hc.ne'

/-! ## Products of boundedly many conjugates

The predicate is written with a *fixed* number `K` of factors and an integer
exponent per factor constrained to `{-1, 0, 1}`; the exponent `0` absorbs an
unused factor, so this is exactly "a product of at most `K` conjugates of `s`
and `s⁻¹`", in a shape whose length does not vary with the index.  Uniform
length is the whole point: an unbounded product of conjugates does not survive
into a metric ultraproduct.

The recursion is written with `Nat.rec` rather than by pattern matching so that
both unfolding lemmas hold definitionally, matching `envelopeSeed` in
`SoficEnvelopeExistence`. -/

/-- `IsBoundedConjProduct s K a` says that `a` is a product of exactly `K`
factors `g * s ^ e * g⁻¹` with each exponent `e` in `{-1, 0, 1}`, hence a
product of at most `K` conjugates of `s` and `s⁻¹`. -/
def IsBoundedConjProduct {G : Type*} [Group G] (s : G) (K : ℕ) (a : G) : Prop :=
  @Nat.rec (fun _ => G → Prop) (fun x => x = 1)
    (fun _ P x => ∃ (g : G) (e : ℤ) (b : G),
      (e = 0 ∨ e = 1 ∨ e = -1) ∧ P b ∧ x = g * s ^ e * g⁻¹ * b) K a

/-- The empty product: at most zero conjugates means the identity. -/
@[simp] theorem isBoundedConjProduct_zero {G : Type*} [Group G] (s a : G) :
    IsBoundedConjProduct s 0 a ↔ a = 1 := Iff.rfl

/-- Peeling off the leading factor.  This is the shape the transfer step
recurses on: one conjugate of a power of `s`, and a shorter product. -/
@[simp] theorem isBoundedConjProduct_succ {G : Type*} [Group G] (s : G) (K : ℕ)
    (a : G) :
    IsBoundedConjProduct s (K + 1) a ↔ ∃ (g : G) (e : ℤ) (b : G),
      (e = 0 ∨ e = 1 ∨ e = -1) ∧ IsBoundedConjProduct s K b ∧
        a = g * s ^ e * g⁻¹ * b := Iff.rfl

/-- The identity is a bounded conjugate product of every length: take every
exponent zero.  This is what makes the predicate inhabited independently of any
theorem about symmetric groups. -/
theorem isBoundedConjProduct_one {G : Type*} [Group G] (s : G) (K : ℕ) :
    IsBoundedConjProduct s K (1 : G) := by
  induction K with
  | zero => exact (isBoundedConjProduct_zero s 1).mpr rfl
  | succ K ih =>
      exact (isBoundedConjProduct_succ s K 1).mpr
        ⟨1, 0, 1, Or.inl rfl, ih, by simp⟩

/-- A bounded conjugate product lies in the normal closure of `s`.  This is the
check that the predicate says what its name says: it *refines* normal generation
by a length bound rather than asserting anything weaker, so a premise phrased
with it cannot be satisfied by elements normal generation would not reach. -/
theorem mem_normalClosure_of_isBoundedConjProduct {G : Type*} [Group G] (s : G) :
    ∀ (K : ℕ) (a : G), IsBoundedConjProduct s K a →
      a ∈ Subgroup.normalClosure ({s} : Set G) := by
  intro K
  induction K with
  | zero =>
      intro a ha
      rw [(isBoundedConjProduct_zero s a).mp ha]
      exact one_mem _
  | succ K ih =>
      intro a ha
      obtain ⟨g, e, b, _, hb, hfac⟩ := (isBoundedConjProduct_succ s K a).mp ha
      have hs : s ∈ Subgroup.normalClosure ({s} : Set G) :=
        Subgroup.subset_normalClosure (Set.mem_singleton_iff.mpr rfl)
      rw [hfac]
      exact mul_mem
        ((Subgroup.normalClosure_normal (s := ({s} : Set G))).conj_mem
          (s ^ e) (zpow_mem hs e) g)
        (ih b hb)

/-- **The transfer step.**  Let `H` be a normal subgroup of the ultraproduct
containing the class of `σ`.  If, for `𝒰`-many indices, `α i` is a product of at
most `K` conjugates of `(σ i)^{±1}` -- with `K` the *same* at every index -- then
`H` contains the class of `α`.

The exponents may still vary with the index, and this is where the ultrafilter
does its work: at each of the `K` factor positions it selects a single exponent,
and the indices that used a different one form a `𝒰`-small set, which
`mk_eq_mk_of_eventually_eq` makes free.  After that selection each factor is
literally a conjugate of a fixed power of `σ` in the product group, so normality
applies. -/
theorem mk_mem_of_eventually_isBoundedConjProduct {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel) (H : Subgroup (UniversalSofic 𝒰 X)) (hH : H.Normal)
    {σ : ∀ i, Equiv.Perm (X i)}
    (hσ : (QuotientGroup.mk σ : UniversalSofic 𝒰 X) ∈ H) :
    ∀ (K : ℕ) (α : ∀ i, Equiv.Perm (X i)),
      (∀ᶠ i in (𝒰 : Filter ι), IsBoundedConjProduct (σ i) K (α i)) →
        (QuotientGroup.mk α : UniversalSofic 𝒰 X) ∈ H := by
  classical
  intro K
  induction K with
  | zero =>
      intro α hα
      have heq : (QuotientGroup.mk α : UniversalSofic 𝒰 X) = 1 := by
        refine (QuotientGroup.eq_one_iff α).mpr ?_
        intro ε hε
        filter_upwards [hα] with i hi
        have h1 : α i = 1 := (isBoundedConjProduct_zero (σ i) (α i)).mp hi
        rw [h1, hammingLength_one]
        exact hε
      rw [heq]
      exact one_mem H
  | succ K ih =>
      intro α hα
      -- A total choice of witnesses, junk outside the `𝒰`-large set.
      have hchoice : ∀ i, ∃ q : Equiv.Perm (X i) × ℤ × Equiv.Perm (X i),
          IsBoundedConjProduct (σ i) (K + 1) (α i) →
            ((q.2.1 = 0 ∨ q.2.1 = 1 ∨ q.2.1 = -1) ∧
              IsBoundedConjProduct (σ i) K q.2.2 ∧
              α i = q.1 * (σ i) ^ q.2.1 * q.1⁻¹ * q.2.2) := by
        intro i
        by_cases hi : IsBoundedConjProduct (σ i) (K + 1) (α i)
        · obtain ⟨g, e, b, he, hb, hfac⟩ :=
            (isBoundedConjProduct_succ (σ i) K (α i)).mp hi
          exact ⟨(g, e, b), fun _ => ⟨he, hb, hfac⟩⟩
        · exact ⟨(1, 0, 1), fun hc => absurd hc hi⟩
      choose q hq using hchoice
      have hev : ∀ᶠ i in (𝒰 : Filter ι),
          ((q i).2.1 = 0 ∨ (q i).2.1 = 1 ∨ (q i).2.1 = -1) ∧
            IsBoundedConjProduct (σ i) K (q i).2.2 ∧
            α i = (q i).1 * (σ i) ^ (q i).2.1 * (q i).1⁻¹ * (q i).2.2 := by
        filter_upwards [hα] with i hi
        exact hq i hi
      -- The ultrafilter picks the exponent of the leading factor.
      obtain ⟨e, he⟩ : ∃ e : ℤ, ∀ᶠ i in (𝒰 : Filter ι), (q i).2.1 = e := by
        rcases 𝒰.em (fun i => (q i).2.1 = 0) with h0 | h0
        · exact ⟨0, h0⟩
        rcases 𝒰.em (fun i => (q i).2.1 = 1) with h1 | h1
        · exact ⟨1, h1⟩
        refine ⟨-1, ?_⟩
        filter_upwards [hev, h0, h1] with i hi hi0 hi1
        rcases hi.1 with hz | ho | hm
        · exact absurd hz hi0
        · exact absurd ho hi1
        · exact hm
      have htail : (QuotientGroup.mk (fun i => (q i).2.2) : UniversalSofic 𝒰 X)
          ∈ H := by
        refine ih (fun i => (q i).2.2) ?_
        filter_upwards [hev] with i hi
        exact hi.2.1
      have hhead : (QuotientGroup.mk
          ((fun i => (q i).1) * σ ^ e * (fun i => (q i).1)⁻¹) :
            UniversalSofic 𝒰 X) ∈ H := by
        have hrw : (QuotientGroup.mk
            ((fun i => (q i).1) * σ ^ e * (fun i => (q i).1)⁻¹) :
              UniversalSofic 𝒰 X)
            = (QuotientGroup.mk (fun i => (q i).1) : UniversalSofic 𝒰 X) *
                (QuotientGroup.mk σ : UniversalSofic 𝒰 X) ^ e *
                (QuotientGroup.mk (fun i => (q i).1) : UniversalSofic 𝒰 X)⁻¹ := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
            QuotientGroup.mk_zpow]
        rw [hrw]
        exact hH.conj_mem ((QuotientGroup.mk σ : UniversalSofic 𝒰 X) ^ e)
          (zpow_mem hσ e) _
      have hprod : (QuotientGroup.mk α : UniversalSofic 𝒰 X)
          = (QuotientGroup.mk
              ((fun i => (q i).1) * σ ^ e * (fun i => (q i).1)⁻¹) :
                UniversalSofic 𝒰 X) *
              QuotientGroup.mk (fun i => (q i).2.2) := by
        rw [← QuotientGroup.mk_mul]
        refine mk_eq_mk_of_eventually_eq 𝒰 X ?_
        filter_upwards [hev, he] with i hi hei
        show α i = ((q i).1 * (σ i) ^ e * ((q i).1)⁻¹) * (q i).2.2
        rw [← hei]
        exact hi.2.2
      rw [hprod]
      exact mul_mem hhead htail

/-! ## Move 2, and the envelope theorem it unlocks

The two declarations below are the only ones in this development that carry the
bounded-normal-generation premise `hBNG`.  Neither may be badged; see the module
docstring. -/

/-- **Simplicity of the universal sofic group, from bounded normal generation of
finite alternating groups.**  Given the premise `hBNG`, the metric ultraproduct of
finite symmetric groups over models whose cardinalities diverge along `𝒰` is a
simple group.

The proof is the manuscript's.  Both the source class and the target class are
put in even form by `exists_even_representative` -- the source so that `hBNG`
never has to speak about an odd `s`, the target because bounded normal
generation reaches only even permutations.  The even source has supports
occupying a positive fraction `δ` of the model on a `𝒰`-large set
(`exists_pos_support_density_of_diverging`); `hBNG` writes each even target
coordinate as a product of at most `K = K(δ)` conjugates, uniformly in the
index; and `mk_mem_of_eventually_isBoundedConjProduct` carries that product into
the normal subgroup. -/
theorem isSimpleGroup_universalSofic {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel)
    (hdiv : ∀ M : ℕ, ∀ᶠ i in (𝒰 : Filter ι), M ≤ Fintype.card (X i))
    (hBNG : ∀ δ : ℝ, 0 < δ → ∃ K M : ℕ,
      ∀ (Y : FiniteModel) (s a : Equiv.Perm Y), M ≤ Fintype.card Y →
        Equiv.Perm.sign s = 1 →
        δ * (Fintype.card Y : ℝ) ≤ ((s.support.card : ℝ)) →
        Equiv.Perm.sign a = 1 → IsBoundedConjProduct s K a) :
    IsSimpleGroup (UniversalSofic 𝒰 X) where
  exists_pair_ne := by
    obtain ⟨z, hz⟩ := exists_ne_one_universalSofic 𝒰 X hdiv
    exact ⟨z, 1, hz⟩
  eq_bot_or_eq_top_of_normal := by
    intro H hH
    rcases eq_or_ne H ⊥ with hbot | hbot
    · exact Or.inl hbot
    refine Or.inr ?_
    obtain ⟨⟨x, hxH⟩, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hx1 : x ≠ 1 := fun hc => hxne (Subtype.ext hc)
    obtain ⟨σ₀, rfl⟩ := QuotientGroup.mk_surjective x
    -- Replace the chosen representative by an even one.  The class is
    -- unchanged, so membership in `H` and nontriviality survive, and `hBNG`
    -- then only ever has to speak about an *even* `s`.
    obtain ⟨σ, hσsign, hσeq⟩ := exists_even_representative 𝒰 X hdiv σ₀
    have hσH : (QuotientGroup.mk σ : UniversalSofic 𝒰 X) ∈ H := by
      rw [hσeq]
      exact hxH
    have hσ1 : (QuotientGroup.mk σ : UniversalSofic 𝒰 X) ≠ 1 := by
      rw [hσeq]
      exact hx1
    obtain ⟨δ, hδ, hdens⟩ :=
      exists_pos_support_density_of_diverging 𝒰 X hdiv σ hσ1
    obtain ⟨K, M, hK⟩ := hBNG δ hδ
    rw [Subgroup.eq_top_iff']
    intro y
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨α, hαsign, hαeq⟩ := exists_even_representative 𝒰 X hdiv τ
    rw [← hαeq]
    refine mk_mem_of_eventually_isBoundedConjProduct 𝒰 X H hH hσH K α ?_
    filter_upwards [hdens, hdiv M] with i hi hMi
    exact hK (X i) (σ i) (α i) hMi (hσsign i) hi (hαsign i)

/-- A countable sofic group embeds into a metric ultraproduct of finite
symmetric groups whose models are nonempty and whose cardinalities diverge along
`𝒰`.  This packages `exists_positive_soficApproximation`,
`exists_soficEmbedding_of_soficApproximation` and `card_eventually_ge` so that
the divergence needed by move 2 travels with the embedding. -/
theorem exists_soficEmbedding_diverging {G : Type*} [Group G] [Countable G]
    (h : IsSofic G) {𝒰 : Ultrafilter ℕ} (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    ∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
      (∀ M : ℕ, ∀ᶠ n in (𝒰 : Filter ℕ), M ≤ Fintype.card (X n)) ∧
      ∃ f : G →* UniversalSofic 𝒰 X, Function.Injective f := by
  obtain ⟨S, hS⟩ := exists_positive_soficApproximation h
  obtain ⟨f, hf⟩ := exists_soficEmbedding_of_soficApproximation S hcof
  exact ⟨S.model, hS, fun M => card_eventually_ge S hcof M, f, hf⟩

/-- **The Elek--Szabó envelope theorem, on the premise `hBNG`.**  Every countable
sofic group embeds in a countable simple sofic group.

All three moves of the classical argument appear: the embedding into the
ultraproduct (`exists_soficEmbedding_diverging`), simplicity of the ultraproduct
(`isSimpleGroup_universalSofic`, the only step using `hBNG`), and the descent to
a countable simple subgroup (`exists_countable_simple_sofic_subgroup`, proved
outright in `SoficEnvelopeExistence`).  The nontrivial element required by the
descent is supplied by the ambient group rather than by `G`, so no nontriviality
hypothesis on `G` is needed. -/
theorem exists_countable_simple_sofic_envelope
    (hBNG : ∀ δ : ℝ, 0 < δ → ∃ K M : ℕ,
      ∀ (Y : FiniteModel) (s a : Equiv.Perm Y), M ≤ Fintype.card Y →
        Equiv.Perm.sign s = 1 →
        δ * (Fintype.card Y : ℝ) ≤ ((s.support.card : ℝ)) →
        Equiv.Perm.sign a = 1 → IsBoundedConjProduct s K a)
    {G : Type*} [Group G] [Countable G] (hG : IsSofic G) :
    ∃ (𝒰 : Ultrafilter ℕ) (X : ℕ → FiniteModel)
      (E : Subgroup (UniversalSofic 𝒰 X)),
      Countable ↥E ∧ IsSimpleGroup ↥E ∧ IsSofic ↥E ∧
        ∃ f : G →* ↥E, Function.Injective f := by
  classical
  obtain ⟨𝒰, hcof⟩ := exists_cofinite_ultrafilter
  obtain ⟨X, hXpos, hdiv, f, hf⟩ := exists_soficEmbedding_diverging hG hcof
  haveI : IsSimpleGroup (UniversalSofic 𝒰 X) :=
    isSimpleGroup_universalSofic 𝒰 X hdiv hBNG
  have hsofic : IsSofic (UniversalSofic 𝒰 X) := isSofic_universalSofic 𝒰 X hXpos
  obtain ⟨z, hz⟩ := exists_ne_one_universalSofic 𝒰 X hdiv
  have hcount : (Set.range f ∪ {z} : Set (UniversalSofic 𝒰 X)).Countable :=
    (Set.countable_range f).union (Set.countable_singleton z)
  obtain ⟨E, hsE, hEc, hEs, hEsofic⟩ :=
    exists_countable_simple_sofic_subgroup hsofic hcount
      (Set.mem_union_right _ (Set.mem_singleton_iff.mpr rfl)) hz
  have hmem : ∀ g : G, f g ∈ E := fun g =>
    SetLike.mem_coe.mp (hsE (Set.mem_union_left _ (Set.mem_range_self g)))
  exact ⟨𝒰, X, E, hEc, hEs, hEsofic, f.codRestrict E hmem,
    (MonoidHom.injective_codRestrict f E hmem).mpr hf⟩

end SoficEnvelopeSimplicity
end GroupApproximation
