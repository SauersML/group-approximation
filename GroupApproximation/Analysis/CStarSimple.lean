import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# C⋆-simplicity

A C⋆-algebra is **simple** when its only *closed* two-sided ideals are `⊥` and `⊤`.  That is the
predicate the operator-algebraic literature means by "simple", and it is what the statement of
STW Problem LIX quantifies over.  This module defines it, over Mathlib vocabulary alone, and
proves that for a unital C⋆-algebra it agrees with the purely algebraic `IsSimpleRing`.

## Why closed ideals, and why the equivalence is still worth having

Closedness is the honest reading of the problem: "simple" in the C⋆ world is a statement about the
lattice of closed ideals, the ones with a C⋆-quotient.  Dropping the closure hypothesis would be a
*different*, a priori stronger, condition, and an endpoint stated with it would be answering a
question nobody asked.

For a **unital** algebra the two conditions coincide, and `isSimpleCStar_iff_isSimpleRing` says so.
The proof is the standard Banach-algebra argument and uses nothing C⋆: a proper two-sided ideal `J`
of a unital Banach algebra contains no unit, so `J ⊆ nonunits`, a *closed* set
(`nonunits.isClosed`, from the openness of the unit group, which is
`HasSummableGeomSeries` and so free from completeness).  Hence `closure J` is again proper, and it
is a closed two-sided ideal; C⋆-simplicity forces it to be `⊥`, so `J = ⊥`.  The converse needs no
analysis at all.

## Contents

* `IsSimpleCStar` --- the predicate, with `[CStarAlgebra A]` as its only instance argument.
  Deliberately **not** `[Nontrivial A]`: the endpoint of Problem LIX reads
  `Nontrivial A → IsSimpleCStar A → …`, and a nontriviality conjunct hidden inside the definition
  would make that statement redundant in a way a reader has to unfold a definition to see.
  Deliberately **not** `[PartialOrder A] [StarOrderedRing A]` either: the endpoint quantifies over
  no order.
* `IsSimpleCStar.eq_top_of_mem` --- the form in which simplicity is used: a closed two-sided ideal
  with a nonzero element is everything.
* `isSimpleCStar_iff_isSimpleRing`.
* `IsSimpleCStar.of_starAlgEquiv` --- transport along a ⋆-isomorphism, which is automatically
  isometric (`StarAlgEquiv.isometry`), so no continuity hypothesis is needed.

Nothing here mentions any particular algebra; in particular nothing here mentions the AH tower of
Problem LIX.  This module is a prerequisite of every statement about that tower, never a
consequence of one.

## Manuscript status

Infrastructure for the LIX endpoint; certifies no manuscript step on its own.
-/

namespace GroupApproximation

universe u v

section Closure

variable {R : Type u} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]

/-- **The closure of a two-sided ideal is two-sided.**  `Ideal.closure` records only that the
closure is a left ideal, because that is all `Submodule` sees; right absorption is the same
argument with `mulRight_continuous` in place of `mulLeft_continuous`. -/
instance isTwoSided_closure (I : Ideal R) [I.IsTwoSided] : I.closure.IsTwoSided := by
  constructor
  intro a b ha
  have ha' : a ∈ closure (I : Set R) := by
    rw [← Ideal.coe_closure]
    exact ha
  have hmaps : Set.MapsTo (fun x : R => x * b) (I : Set R) (I : Set R) :=
    fun _ hy => I.mul_mem_right b hy
  have hmem := map_mem_closure (f := fun x : R => x * b) (continuous_mul_const b) ha' hmaps
  rw [← Ideal.coe_closure] at hmem
  exact hmem

end Closure

section Def

variable (A : Type u) [CStarAlgebra A]

/-- **C⋆-simplicity**: every closed two-sided ideal is `⊥` or `⊤`.

This is the predicate STW Problem LIX quantifies over.  It is *not* Mathlib's `IsSimpleRing`,
which asks the same of every two-sided ideal, closed or not; for a unital C⋆-algebra the two agree
(`isSimpleCStar_iff_isSimpleRing`), but the endpoint should say what was asked. -/
def IsSimpleCStar : Prop :=
  ∀ I : Ideal A, I.IsTwoSided → IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

end Def

namespace IsSimpleCStar

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- Simplicity applied to an ideal whose two-sidedness is an instance. -/
theorem eq_bot_or_eq_top (h : IsSimpleCStar A) (I : Ideal A) [I.IsTwoSided]
    (hI : IsClosed (I : Set A)) : I = ⊥ ∨ I = ⊤ :=
  h I inferInstance hI

/-- **The working form of simplicity**: a closed two-sided ideal containing a nonzero element is
everything. -/
theorem eq_top_of_mem (h : IsSimpleCStar A) {I : Ideal A} [I.IsTwoSided]
    (hI : IsClosed (I : Set A)) {x : A} (hxI : x ∈ I) (hx : x ≠ 0) : I = ⊤ := by
  rcases h.eq_bot_or_eq_top I hI with hbot | htop
  · exact absurd (Ideal.mem_bot.mp (hbot ▸ hxI)) hx
  · exact htop

/-- **Simplicity transports along a ⋆-isomorphism.**  A ⋆-isomorphism of C⋆-algebras is an
isometry (`StarAlgEquiv.isometry`), so the preimage of a closed ideal is closed, and no continuity
hypothesis is required. -/
theorem of_starAlgEquiv (e : A ≃⋆ₐ[ℂ] B) (h : IsSimpleCStar A) : IsSimpleCStar B := by
  intro I hI hIclosed
  haveI := hI
  have hcont : Continuous (e : A → B) := (StarAlgEquiv.isometry e).continuous
  set J : Ideal A := Ideal.comap (e : A ≃⋆ₐ[ℂ] B) I with hJ
  haveI : J.IsTwoSided := by
    refine ⟨fun b hx => ?_⟩
    have hx' : e _ ∈ I := hx
    have : e _ * e b ∈ I := I.mul_mem_right _ hx'
    simpa [hJ, Ideal.comap, map_mul] using this
  have hJclosed : IsClosed (J : Set A) := by
    have : (J : Set A) = (e : A → B) ⁻¹' (I : Set B) := rfl
    rw [this]
    exact hIclosed.preimage hcont
  rcases h J inferInstance hJclosed with hbot | htop
  · left
    refine (Submodule.eq_bot_iff I).mpr fun x hx => ?_
    have hmem : e.symm x ∈ J := by
      have : e (e.symm x) ∈ I := by simpa using hx
      simpa [hJ, Ideal.comap] using this
    have : e.symm x = 0 := Ideal.mem_bot.mp (hbot ▸ hmem)
    have := congrArg (fun y => e y) this
    simpa using this
  · right
    refine (Ideal.eq_top_iff_one I).mpr ?_
    have h1 : (1 : A) ∈ J := htop ▸ Submodule.mem_top
    have : e (1 : A) ∈ I := h1
    simpa using this

end IsSimpleCStar

/-- **C⋆-simplicity and ring simplicity agree for a unital C⋆-algebra.**

`←` is trivial: a closed two-sided ideal is in particular a two-sided ideal.

`→` is the Banach-algebra argument.  Let `J` be a two-sided ideal with `J ≠ ⊤`.  Then `J` contains
no unit, so `(J : Set A) ⊆ nonunits A`; the latter is closed, so `closure J ⊆ nonunits A` and in
particular `1 ∉ closure J`, i.e. `J.closure ≠ ⊤` (Mathlib packages exactly this as
`Ideal.closure_ne_top`).  Now `J.closure` is a *closed two-sided* ideal, so C⋆-simplicity makes it
`⊥`, and `J ≤ J.closure` forces `J = ⊥`. -/
theorem isSimpleCStar_iff_isSimpleRing (A : Type u) [CStarAlgebra A] [Nontrivial A] :
    IsSimpleCStar A ↔ IsSimpleRing A := by
  constructor
  · intro h
    refine IsSimpleRing.of_eq_bot_or_eq_top fun J => ?_
    by_cases hJ : J.asIdeal = ⊤
    · right
      refine eq_top_iff.mpr ?_
      rw [SetLike.le_def]
      intro x _
      have hx : x ∈ J.asIdeal := hJ ▸ Submodule.mem_top
      exact TwoSidedIdeal.mem_asIdeal.mp hx
    · left
      have hne : J.asIdeal.closure ≠ ⊤ := J.asIdeal.closure_ne_top hJ
      have hclosed : IsClosed ((J.asIdeal.closure : Ideal A) : Set A) := isClosed_closure
      rcases h J.asIdeal.closure inferInstance hclosed with hbot | htop
      · refine eq_bot_iff.mpr ?_
        rw [SetLike.le_def]
        intro x hx
        have hx' : x ∈ J.asIdeal.closure :=
          subset_closure (TwoSidedIdeal.mem_asIdeal.mpr hx)
        have hzero : x = 0 := Ideal.mem_bot.mp (hbot ▸ hx')
        simpa using hzero
      · exact absurd htop hne
  · intro h I hI _
    haveI := hI
    rcases eq_bot_or_eq_top I.toTwoSided with h' | h'
    · left
      rw [← Ideal.asIdeal_toTwoSided I, h', TwoSidedIdeal.bot_asIdeal]
    · right
      rw [← Ideal.asIdeal_toTwoSided I, h', TwoSidedIdeal.top_asIdeal]

end GroupApproximation
