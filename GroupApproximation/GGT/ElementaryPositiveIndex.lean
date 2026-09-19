import GroupApproximation.GGT.DGOCorollary66

/-!
# The orientation-preserving part of `E(h)` has index at most two

`GGT/DGOCorollary66.lean` defines `positiveElementaryClosure h` --- the elements
inverse-conjugating some nonzero power of `h` to itself --- and proves DGO
Corollary 6.6 against it: under the finite-transversal conclusion of Lemma 6.5
it is the centralizer of one positive power.  What it does not record is the
structure of that set inside `elementaryClosure h`, which is what every consumer
of the `E = E⁺` question actually needs.  This module supplies it.

## What is here

* `mem_positiveElementaryClosure_iff_commute` --- `E⁺(h)` is exactly the union
  of the centralizers of the nonzero powers of `h`.  The definition's
  `g⁻¹ * h ^ n * g = h ^ n` says precisely `Commute g (h ^ n)`, which makes the
  orientation convention irrelevant on the positive part and makes the closure
  properties one line each.
* `positiveElementaryClosureSubgroup` --- `E⁺(h)` as a `Subgroup`, with its
  carrier proved equal to the set.  Closure under multiplication takes the
  product `n * m` of the two exponents; both factors then commute with
  `h ^ (n * m)` because it is a power of `h ^ n` and also of `h ^ m`.
* `positiveElementaryClosure_le_elementaryClosure` --- `E⁺(h) ≤ E(h)`,
  unconditionally.  No loxodromy is needed in this direction.
* `sq_mem_positiveElementaryClosure` --- **for loxodromic `h`, the square of
  every element of `E(h)` lies in `E⁺(h)`.**

## What this does for `NonElSub`'s fourth clause

`coe_elementaryClosure_eq_positive_of_centralizes` is stated in the exact `Set`
form that `GGT.HullYiStatements.NonElSub`'s fourth clause uses,
`(elementaryClosure f : Set G) = positiveElementaryClosure f`.  So that clause
now has a **single identified producer**: when DGO 4.21(b) lands, the clause is
discharged *through a named lemma* rather than restated at the call site.  Its
hardest-looking conjunct is no longer an open statement but a statement with a
route.

The clause is also **necessary**, not merely convenient.  Given DGO Corollary
6.6 (`E⁺ = C_G(f^r)`, proved in `DGOCorollary66`), `E = E⁺` is *equivalent* to
Hull's condition (1), by `elementaryClosure_eq_positive_of_centralizes` in one
direction and Corollary 6.6 in the other.  It cannot be dropped or weakened
while keeping `yi`'s component-matching step.

## Why the square lemma is the useful form

`conj_zpow_eq_or_of_mem_elementaryClosure` says every `a ∈ E(h)` conjugates some
`hⁿ` to `h^{±n}`.  The sign is well defined --- both would give `h ^ (2 * n) = 1`,
impossible for a loxodromic --- and it multiplies, so it is a homomorphism
`E(h) → ℤ/2` whose kernel is `E⁺(h)`.  Hence `E⁺(h)` has index at most two.

Rather than build the quotient map, the content is recorded in the form a
consumer reaches for: `a ^ 2 ∈ E⁺(h)` for every `a ∈ E(h)`, unconditionally on
orientation.  In the reversing case `a * h ^ n * a⁻¹ = h ^ (-n)`, conjugating a
second time returns `h ^ n`, which is the whole proof.  Anything that needs to
get from `E(h)` into `E⁺(h)` and can tolerate passing to a square needs neither
orientation-purity nor a new citation.

**`yi`'s matching step is not such a consumer**, and the reason is worth
recording so the idea is not retried.  Its telescoping is
`Lab(e₁) = a₁⁻¹ c a₁ = c`, which needs `c` itself --- with only `c² ∈ C_G(a₁)`
the chain never starts.  And its conclusion is about `c`: `c² = 1` says only
that `c` is an involution, which is exactly the case `yi` must exclude, namely
`E(h) = ⟨h⟩ × ⟨c⟩` with `c` of order two.  The square lemma is kept because it is
the honest content of "index at most two", not because it discharges anything
here.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## `E⁺` is the union of the centralizers of the nonzero powers -/

/-- Membership in `E⁺(h)` is commutation with some nonzero power of `h`.  The
definition's `g⁻¹ * h ^ n * g = h ^ n` is that statement written with the
conjugation spelled out. -/
theorem mem_positiveElementaryClosure_iff_commute {h g : G} :
    g ∈ positiveElementaryClosure h ↔ ∃ n : ℤ, n ≠ 0 ∧ Commute g (h ^ n) := by
  constructor
  · rintro ⟨n, hn, he⟩
    refine ⟨n, hn, ?_⟩
    have hstep : g * (g⁻¹ * h ^ n * g) = g * h ^ n := by rw [he]
    have hleft : h ^ n * g = g * h ^ n := by
      rw [← hstep]
      group
    exact hleft.symm
  · rintro ⟨n, hn, hc⟩
    refine ⟨n, hn, ?_⟩
    rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]

/-! ## The subgroup structure -/

/-- **`E⁺(h)` as a subgroup.**  Closure under multiplication takes the product
of the two exponents: `h ^ (n * m)` is a power of `h ^ n` and also of `h ^ m`,
so both factors commute with it. -/
def positiveElementaryClosureSubgroup (h : G) : Subgroup G where
  carrier := positiveElementaryClosure h
  one_mem' := by
    refine mem_positiveElementaryClosure_iff_commute.mpr ⟨1, one_ne_zero, ?_⟩
    exact Commute.one_left _
  mul_mem' := by
    intro a b ha hb
    obtain ⟨n, hn, hca⟩ := mem_positiveElementaryClosure_iff_commute.mp ha
    obtain ⟨m, hm, hcb⟩ := mem_positiveElementaryClosure_iff_commute.mp hb
    refine mem_positiveElementaryClosure_iff_commute.mpr ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have hpa : Commute a (h ^ (n * m)) := by
      rw [zpow_mul]
      exact hca.zpow_right m
    have hpb : Commute b (h ^ (n * m)) := by
      rw [mul_comm, zpow_mul]
      exact hcb.zpow_right n
    exact hpa.mul_left hpb
  inv_mem' := by
    intro a ha
    obtain ⟨n, hn, hca⟩ := mem_positiveElementaryClosure_iff_commute.mp ha
    exact mem_positiveElementaryClosure_iff_commute.mpr ⟨n, hn, hca.inv_left⟩

@[simp] theorem coe_positiveElementaryClosureSubgroup (h : G) :
    (positiveElementaryClosureSubgroup h : Set G) = positiveElementaryClosure h :=
  rfl

@[simp] theorem mem_positiveElementaryClosureSubgroup {h g : G} :
    g ∈ positiveElementaryClosureSubgroup h ↔ g ∈ positiveElementaryClosure h :=
  Iff.rfl

/-! ## `E⁺(h) ≤ E(h)`, unconditionally -/

/-- The orientation-preserving part sits inside the elementary closure, with no
hypothesis on `h`: commuting with `h ^ n` conjugates `h ^ n` to itself, which is
a witness for membership with both exponents equal. -/
theorem positiveElementaryClosure_le_elementaryClosure (h : G) :
    positiveElementaryClosureSubgroup h ≤ elementaryClosure h := by
  intro a ha
  obtain ⟨n, hn, hca⟩ := mem_positiveElementaryClosure_iff_commute.mp ha
  refine mem_elementaryClosure.mpr ⟨n, n, hn, hn, ?_⟩
  have hleft : a * h ^ n = h ^ n * a := hca
  calc a * h ^ n * a⁻¹ = h ^ n * a * a⁻¹ := by rw [hleft]
    _ = h ^ n := by group

/-! ## Squares land in `E⁺` -/

/-- **The square of any element of `E(h)` is orientation-preserving**, for `h`
loxodromic.  Conjugating twice by an element that reverses `hⁿ` returns `hⁿ`, so
no purity hypothesis is needed to get from `E(h)` into `E⁺(h)` at the cost of a
square.  This is the concrete form of "`E⁺(h)` has index at most two". -/
theorem sq_mem_positiveElementaryClosure (hiso : IsIsometricAction G X)
    {h a : G} {x : X} (hlox : IsLoxodromic h x)
    (ha : a ∈ elementaryClosure h) :
    a ^ 2 ∈ positiveElementaryClosure h := by
  obtain ⟨n, hn, hcase⟩ :=
    conj_zpow_eq_or_of_mem_elementaryClosure hiso hlox ha
  refine ⟨n, hn, ?_⟩
  have hkey : a ^ 2 * h ^ n * (a ^ 2)⁻¹ = h ^ n := by
    have hsq : a ^ 2 * h ^ n * (a ^ 2)⁻¹ = a * (a * h ^ n * a⁻¹) * a⁻¹ := by
      rw [sq]
      group
    rcases hcase with hpos | hneg
    · rw [hsq, hpos, hpos]
    · rw [hsq, hneg]
      have hinv : a * h ^ (-n) * a⁻¹ = (a * h ^ n * a⁻¹)⁻¹ := by group
      rw [hinv, hneg]
      group
  have hcomm : a ^ 2 * h ^ n = h ^ n * a ^ 2 := by
    have hmul := congrArg (fun t : G => t * a ^ 2) hkey
    simpa using hmul
  rw [mul_assoc, ← hcomm, inv_mul_cancel_left]

/-! ## Hull's condition (1) forces orientation-purity

The converse direction, and the reason `NonElSub`'s fourth clause cannot be
dropped: if `E(f)` *is* the centralizer of a nonzero power --- Hull's condition
(1), which is what DGO Corollary 6.6 delivers for `E⁺` --- then every element of
`E(f)` centralizes that power and so lies in `E⁺(f)` already.  So `E = E⁺` is not
one route to condition (1); given `E⁺ = C_G(f^r)` it is *equivalent* to it.

Dually an orientation-reverser can never centralize a nonzero power: `g⁻¹ fⁿ g`
cannot equal both `fⁿ` and `f^{-n}` unless `f ^ (2 * n) = 1`, which a loxodromic
forbids.  That is the same computation that makes the sign well defined, so the
two facts land together. -/

/-- **Condition (1) implies orientation-purity, containment form.** -/
theorem elementaryClosure_le_positive_of_centralizes {f : G} {n : ℤ} (hn : n ≠ 0)
    (hE : ∀ g ∈ elementaryClosure f, Commute g (f ^ n)) :
    elementaryClosure f ≤ positiveElementaryClosureSubgroup f := by
  intro g hg
  exact mem_positiveElementaryClosure_iff_commute.mpr ⟨n, hn, hE g hg⟩

/-- **Condition (1) implies `E(f) = E⁺(f)`.**  With
`positiveElementaryClosure_le_elementaryClosure` for the reverse containment. -/
theorem elementaryClosure_eq_positive_of_centralizes {f : G} {n : ℤ} (hn : n ≠ 0)
    (hE : ∀ g ∈ elementaryClosure f, Commute g (f ^ n)) :
    elementaryClosure f = positiveElementaryClosureSubgroup f :=
  le_antisymm (elementaryClosure_le_positive_of_centralizes hn hE)
    (positiveElementaryClosure_le_elementaryClosure f)

/-- The set form, which is how `GGT.HullYiStatements.NonElSub` states its fourth
clause. -/
theorem coe_elementaryClosure_eq_positive_of_centralizes {f : G} {n : ℤ}
    (hn : n ≠ 0) (hE : ∀ g ∈ elementaryClosure f, Commute g (f ^ n)) :
    (elementaryClosure f : Set G) = positiveElementaryClosure f := by
  rw [elementaryClosure_eq_positive_of_centralizes hn hE]
  rfl

end Elementary
end GGT
end GroupApproximation
