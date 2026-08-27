import GroupApproximation.Steinberg.GeneralRankFiniteFieldPropertyT

/-!
# Finitely generated rings, and the printed hypothesis of the EJZ theorem

The Ershov--Jaikin-Zapirain theorem is printed with the hypothesis "`R` is a
finitely generated (associative) ring with `1`".  The Lean development states
its coefficient hypothesis as `Algebra.FiniteType (ZMod p) A` instead.  Those
are the same condition, but that was not proved anywhere, so the Lean was
carrying a *different* hypothesis from the printed one.  This file closes the
gap.

## What Mathlib has, and does not have

Mathlib has **no notion of "finitely generated as a ring"**: there is no
`Subring.FG`, no `Subsemiring.FG`, and no `Ring.FG`.  `Subalgebra.FG` and
`Algebra.FiniteType` exist, but they are relative to a base ring.  So the
printed phrase has to be defined here, and `IsFinitelyGeneratedRing` does
that in the only reading that matches the source: generated as a ring with
`1` by a finite subset, i.e. `Subring.closure s = ⊤` for some
`s : Finset A`.

That is the right reading.  Ershov--Jaikin-Zapirain, *Property (T) for
noncommutative universal lattices*, Theorem 1.1 says "finitely generated
(associative) ring with 1", and the Remark immediately after it says the
theorem is equivalent to the statement for `R = ℤ⟨x₁, …, x_d⟩` -- i.e. the
finitely generated rings are exactly the quotients of the free associative
`ℤ`-algebras on finitely many generators, which is precisely
`Subring.closure s = ⊤` for a finite `s`.  Nothing about commutativity is
assumed, and `Subring` in Mathlib does not assume it either.

## Main results

* `IsFinitelyGeneratedRing` -- the printed notion.
* `mem_adjoin_iff_mem_closure` -- over a base ring whose image lands in every
  subring, `Algebra.adjoin` and `Subring.closure` have the same members.
* `isFinitelyGeneratedRing_iff_finiteType` -- hence the two finiteness
  notions agree, in **both** directions.
* `isFinitelyGeneratedRing_iff_finiteType_zmod` and
  `isFinitelyGeneratedRing_iff_finiteType_int` -- the two instances that
  matter: `ZMod p` and `ℤ`.
* `primeCharFinitelyGeneratedRingElementaryPropertyT` -- the advertised
  endpoint, now carrying the manuscript's own hypothesis.

## Why the base ring drops out

`Algebra.adjoin R s` is the smallest subring containing `s` *and the image of
`R`* (`Algebra.mem_adjoin_iff`).  When that image lies in every subring --
which happens exactly when `algebraMap` factors through the prime subring --
the second clause is free and the two closures coincide.  Both `ℤ` and
`ZMod p` have that property, `ℤ` because `algebraMap` is the integer cast,
and `ZMod p` because every element of `ZMod p` is an integer cast
(`ZMod.intCast_surjective`) and every subring contains every integer (the
root-namespace `intCast_mem`, which is stated for `SubringClass` rather than
for `Subring`).  So no characteristic hypothesis is needed for the
equivalence itself; `CharP A p` is needed only to *have* the `ZMod p`-algebra
structure, and Mathlib's `Subsingleton (Algebra (ZMod p) A)` means it does
not matter which such structure is used.
-/

namespace GroupApproximation

/-- **A ring is finitely generated** when some finite subset generates it as a
ring with `1`.  This is the hypothesis printed in Ershov--Jaikin-Zapirain
Theorem 1.1; Mathlib has no notion of it, so it is defined here. -/
def IsFinitelyGeneratedRing (A : Type*) [Ring A] : Prop :=
  ∃ s : Finset A, Subring.closure (s : Set A) = ⊤

/-! ### The base ring drops out of the closure -/

section Bridge

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- When the image of the base ring lies in every subring, adjoining a set as
an `R`-algebra and generating it as a ring produce the same elements. -/
theorem mem_adjoin_iff_mem_closure
    (hR : ∀ (r : R) (T : Subring A), algebraMap R A r ∈ T) (s : Set A) (x : A) :
    x ∈ Algebra.adjoin R s ↔ x ∈ Subring.closure s := by
  rw [Algebra.mem_adjoin_iff]
  have hclosure : Subring.closure (Set.range (algebraMap R A) ∪ s) =
      Subring.closure s := by
    refine le_antisymm
      (Subring.closure_le.2 (Set.union_subset ?_ Subring.subset_closure))
      (Subring.closure_mono Set.subset_union_right)
    rintro _ ⟨r, rfl⟩
    exact hR r _
  rw [hclosure]

/-- **The two finiteness notions agree, in both directions**, for any base
ring whose image lies in every subring. -/
theorem isFinitelyGeneratedRing_iff_finiteType
    (hR : ∀ (r : R) (T : Subring A), algebraMap R A r ∈ T) :
    IsFinitelyGeneratedRing A ↔ Algebra.FiniteType R A := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨⟨s, ?_⟩⟩
    rw [Algebra.eq_top_iff]
    intro x
    refine (mem_adjoin_iff_mem_closure hR (s : Set A) x).2 ?_
    rw [hs]
    exact Subring.mem_top x
  · rintro ⟨⟨s, hs⟩⟩
    refine ⟨s, ?_⟩
    rw [Subring.eq_top_iff']
    intro x
    refine (mem_adjoin_iff_mem_closure hR (s : Set A) x).1 ?_
    rw [hs]
    exact Algebra.mem_top

end Bridge

/-! ### The two base rings that matter -/

/-- Every subring contains the image of `ZMod p`, because every element of
`ZMod p` is an integer cast and every subring contains every integer. -/
theorem algebraMap_zmod_mem_subring (p : ℕ) {A : Type*} [Ring A]
    [Algebra (ZMod p) A] (r : ZMod p) (T : Subring A) :
    algebraMap (ZMod p) A r ∈ T := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective r
  rw [map_intCast]
  exact intCast_mem T k

/-- **The equivalence over `ZMod p`.**  No characteristic hypothesis appears:
`CharP A p` is what supplies the `ZMod p`-algebra structure, and by
`ZMod.instSubsingletonAlgebra` any two such structures agree, so the
statement is insensitive to which one is in scope. -/
theorem isFinitelyGeneratedRing_iff_finiteType_zmod (p : ℕ) (A : Type*)
    [Ring A] [Algebra (ZMod p) A] :
    IsFinitelyGeneratedRing A ↔ Algebra.FiniteType (ZMod p) A :=
  isFinitelyGeneratedRing_iff_finiteType
    (fun r T ↦ algebraMap_zmod_mem_subring p r T)

/-- **The equivalence over `ℤ`.**  Every ring is a `ℤ`-algebra, so this says
that Mathlib's `Algebra.FiniteType ℤ A` is exactly the printed notion of a
finitely generated ring, with no hypothesis at all. -/
theorem isFinitelyGeneratedRing_iff_finiteType_int (A : Type*) [Ring A] :
    IsFinitelyGeneratedRing A ↔ Algebra.FiniteType ℤ A :=
  isFinitelyGeneratedRing_iff_finiteType
    (fun k T ↦ intCast_mem T k)

/-! ### Calibration

`IsFinitelyGeneratedRing` is a new definition, and a definition that nothing
satisfies would make every theorem stated with it vacuous.  One concrete
witness is therefore checked here, and carried through to a concrete
property-`(T)` conclusion below. -/

/-- `ZMod p` is finitely generated as a ring, by the empty set: every element
is an integer cast, and every subring contains every integer. -/
theorem isFinitelyGeneratedRing_zmod (p : ℕ) :
    IsFinitelyGeneratedRing (ZMod p) := by
  refine ⟨∅, ?_⟩
  rw [Subring.eq_top_iff']
  intro x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  exact intCast_mem _ k

/-! ### The EJZ corollary, with the printed hypothesis -/

/-- **Property `(T)` for `EL_n(A)`, every `n ≥ 3`, over every finitely
generated ring of prime characteristic** -- stated with the manuscript's own
coefficient hypothesis rather than with `Algebra.FiniteType`.

`primeCharGeneralRankElementary_hasKazhdanPropertyT` proves the same thing
with `Algebra.FiniteType (ZMod p) A` in place of `IsFinitelyGeneratedRing A`;
`isFinitelyGeneratedRing_iff_finiteType_zmod` is what licenses the exchange. -/
theorem primeCharFinitelyGeneratedRingElementary_hasKazhdanPropertyT
    (p : ℕ) (hp : p.Prime) (A : Type) [Ring A] [CharP A p]
    (hfg : IsFinitelyGeneratedRing A) (n : ℕ) (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) A) := by
  letI : Algebra (ZMod p) A := ZMod.algebra A p
  exact primeCharGeneralRankElementary_hasKazhdanPropertyT p hp A
    ((isFinitelyGeneratedRing_iff_finiteType_zmod p A).1 hfg) n hn

/-- **The conclusion is not vacuous**: the endpoint below produces property
`(T)` for a concrete family of groups, `EL_n(ZMod p)` for every prime `p` and
every `n ≥ 3`.  This is the calibration of `isFinitelyGeneratedRing_zmod`
carried through the corollary. -/
theorem zmodPrime_elementary_hasKazhdanPropertyT (p : ℕ) (hp : p.Prime)
    (n : ℕ) (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) (ZMod p)) :=
  primeCharFinitelyGeneratedRingElementary_hasKazhdanPropertyT p hp (ZMod p)
    (isFinitelyGeneratedRing_zmod p) n hn

/-- The advertised endpoint: the Ershov--Jaikin-Zapirain theorem in every rank
`n ≥ 3` over every finitely generated ring of prime characteristic, with the
printed hypothesis.

Characteristic zero and non-prime positive characteristic are **not**
covered; see `Steinberg/GeneralRankFiniteFieldPropertyT.lean` for exactly
which half of the certificate is missing in each case. -/
def PrimeCharFinitelyGeneratedRingElementaryPropertyT : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (A : Type) [Ring A] [CharP A p],
    IsFinitelyGeneratedRing A → ∀ (n : ℕ), 3 ≤ n →
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) A)

theorem primeCharFinitelyGeneratedRingElementaryPropertyT :
    PrimeCharFinitelyGeneratedRingElementaryPropertyT := by
  intro p hp A _ _ hfg n hn
  exact primeCharFinitelyGeneratedRingElementary_hasKazhdanPropertyT p hp A hfg n hn

end GroupApproximation
