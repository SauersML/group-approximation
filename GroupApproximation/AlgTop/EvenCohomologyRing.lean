import GroupApproximation.AlgTop.CupAssoc

/-!
# The even part of `H^*(X; R)`, reindexed, and where its ring structure comes from

`GroupApproximation.AlgTop.TotalChern` is stated over a single `CommRing A`.  The
`A` the Chern-class layer wants is the **even** cohomology

```text
A = ⨁_{n : ℕ} H^{2n}(X; R),
```

because Chern classes live in even degrees only, and because graded
commutativity in even total degree is honest commutativity.  This file is the
reindexing `n ↦ 2n` together with its multiplication, so that every degree cast
in the whole Chern development is confined to one place — the single cast
`2m + 2n = 2(m + n)` in `evenCup`.

That is the concrete answer to the foundation plan's standing rule that every
degree-arithmetic mismatch must go through `cohCast`: downstream of this file
there is no dependent degree arithmetic at all, because a total Chern class is a
`PowerSeries A` whose variable carries the degree and whose coefficient type is
the fixed `A`.

## What is here and what is missing

Present: the reindexed groups `Ev`, the product `evenCup`, the unit, unitality,
associativity and bilinearity — all of them consequences of `cup_assoc`,
`cup_one`, `one_cup` and the bilinearity of `cup`, which
`GroupApproximation/AlgTop/{CupProduct,CupAssoc}.lean` already prove.

Missing, and it is the only thing missing: **commutativity**

```lean
theorem evenCup_comm {m n : ℕ} (a : Ev R X m) (b : Ev R X n) :
    (cohCast R X (by ring : 2 * (m + n) = 2 * (n + m))).hom (evenCup a b) = evenCup b a
```

which is the even case of graded commutativity, with sign `+1`, scheduled in
`AlgTop/CupCommutativity.lean`.  Once it exists, `⨁ n, Ev R X n` is a `CommRing`
by `DirectSum.GCommRing` and `DirectSum.commRing`
(`Mathlib/Algebra/DirectSum/Ring.lean`), whose remaining fields are exactly the
lemmas below — so the packaging is an instance declaration, not a construction.

## Status

Authored against the API contract in `notes/algtop-foundation-plan-2026-09-05.md`
and the signatures actually present in `SingularCohomology.lean`,
`CupProduct.lean` and `CupAssoc.lean`.  It has not been compiled: the cohomology
lane's modules were not green when this was written and the fleet build mutex has
been held elsewhere.  Treat every proof here as unverified until a build log says
otherwise.
-/

namespace GroupApproximation
namespace AlgTop
namespace EvenCohomology

open CategoryTheory

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- The even part of the cohomology of `X`, reindexed so that `Ev R X n` is
`H^{2n}(X; R)`.  The reindexing is what turns the `ℕ`-graded cup product into a
grading whose total degree is additive on the *reindexed* degrees. -/
abbrev Ev (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R :=
  cohomology R X (2 * n)

/-- The product on the even part.  This is the **only** degree cast in the Chern
development: `cup` lands in degree `2m + 2n` and the reindexed target is
`2(m + n)`. -/
noncomputable def evenCup {m n : ℕ} (a : Ev R X m) (b : Ev R X n) : Ev R X (m + n) :=
  (cohCast R X (by ring : 2 * m + 2 * n = 2 * (m + n))).hom (a ⌣ b)

/-- The unit of the even part.  No cast: `2 * 0` reduces to `0`. -/
noncomputable def evenOne (R : Type) [CommRing R] (X : TopCat.{0}) : Ev R X 0 := one R X

@[simp] theorem evenCup_add_left {m n : ℕ} (a a' : Ev R X m) (b : Ev R X n) :
    evenCup (a + a') b = evenCup a b + evenCup a' b := by
  simp only [evenCup, cup_add_left, map_add]

@[simp] theorem evenCup_add_right {m n : ℕ} (a : Ev R X m) (b b' : Ev R X n) :
    evenCup a (b + b') = evenCup a b + evenCup a b' := by
  simp only [evenCup, cup_add_right, map_add]

@[simp] theorem evenCup_smul_left {m n : ℕ} (s : R) (a : Ev R X m) (b : Ev R X n) :
    evenCup (s • a) b = s • evenCup a b := by
  simp only [evenCup, cup_smul_left, map_smul]

@[simp] theorem evenCup_smul_right {m n : ℕ} (s : R) (a : Ev R X m) (b : Ev R X n) :
    evenCup a (s • b) = s • evenCup a b := by
  simp only [evenCup, cup_smul_right, map_smul]

/-- Right unitality on the even part.  Both `2 * m + 2 * 0` and `2 * (m + 0)`
reduce to `2 * m`, so the cast is a transport along a reflexive equation. -/
@[simp] theorem evenCup_one {m : ℕ} (a : Ev R X m) : evenCup a (evenOne R X) = a := by
  rw [evenCup, evenOne, cup_one]
  exact cohCast_self_apply R X _ a

/-- Left unitality on the even part. -/
@[simp] theorem one_evenCup {n : ℕ} (b : Ev R X n) : evenCup (evenOne R X) b = b := by
  rw [evenCup, evenOne, one_cup, cohCast_comp]
  exact cohCast_self_apply R X _ b

/-- A degree transport on the left factor moves out of a cup product. -/
theorem cohCast_cup_left {p p' q : ℕ} (h : p = p') (a : cohomology R X p)
    (b : cohomology R X q) :
    (cohCast R X h).hom a ⌣ b
      = (cohCast R X (by rw [h] : p + q = p' + q)).hom (a ⌣ b) := by
  subst h
  simp

/-- A degree transport on the right factor moves out of a cup product. -/
theorem cohCast_cup_right {p q q' : ℕ} (h : q = q') (a : cohomology R X p)
    (b : cohomology R X q) :
    a ⌣ (cohCast R X h).hom b
      = (cohCast R X (by rw [h] : p + q = p + q')).hom (a ⌣ b) := by
  subst h
  simp

/-- Associativity on the even part, with the degree transport written out.  This
is `cup_assoc` with the two `evenCup` casts absorbed; the three transports
collapse by `cohCast_comp`, and two transports between the same pair of degrees
are equal by proof irrelevance. -/
theorem evenCup_assoc {m n p : ℕ} (a : Ev R X m) (b : Ev R X n) (c : Ev R X p) :
    (cohCast R X (by ring : 2 * (m + n + p) = 2 * (m + (n + p)))).hom
        (evenCup (evenCup a b) c)
      = evenCup a (evenCup b c) := by
  have hassoc : a ⌣ (b ⌣ c)
      = (cohCast R X (add_assoc (2 * m) (2 * n) (2 * p))).hom ((a ⌣ b) ⌣ c) :=
    (cup_assoc a b c).symm
  simp only [evenCup]
  rw [cohCast_cup_left, cohCast_cup_right, hassoc, cohCast_comp, cohCast_comp,
    cohCast_comp]

end EvenCohomology
end AlgTop
end GroupApproximation
