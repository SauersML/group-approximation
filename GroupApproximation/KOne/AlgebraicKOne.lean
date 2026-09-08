import GroupApproximation.KOne.StableWhitehead
import GroupApproximation.Algebra.CountableMatrixUnits

/-!
# `K₁(R)` for an arbitrary ring, and the canonical map `κ : Rˣ → K₁(R)`

`non_mf_groups_exist.tex`, the paragraph preceding Theorem
`thm:mf-quotient-units`:

> Let `GL(R)` and `EL(R)` be the direct limits of `GL_n(R)` and `EL_n(R)` along
> `A ↦ diag(A, 1)`; the subgroup `EL(R)` is normal in `GL(R)` by Whitehead's
> lemma, and `K_1(R) = GL(R)/EL(R)`.  Write `κ : R^× → K_1(R)` for the canonical
> map.

`KOne/ClassicalKOne.lean` built `GL(R)` and `EL(R)` generically; `KOne/StableWhitehead.lean`
proved the normality.  This module takes the quotient, names it, and gives it
the two adjectives the printed proof of `thm:mf-quotient-units` uses of it:
**abelian** and, for countable `R`, **countable**.

## Why this object is needed

`Manuscript/OneSidedMFRadical/MFQuotientUnits.lean` states the printed theorem
with the quotient as *"some countable abelian MF group with an isomorphism onto
it"*, and its own docstring records the cost: naming the quotient `K_1(R)` needs
the colimit `lim GL_n/EL_n`, which was not built for a general ring.  The
manuscript's content is that the obstruction *is* the K-theory, and a statement
that never names `K_1` cannot carry that.  With this module the printed
identification can be stated on the nose.

## Relation to the two `K₁`s already in the tree

* `KOne/WhiteheadQuotient.lean` has `BinaryLeavittWhiteheadK1`, the rank-one
  Whitehead quotient `Lˣ / stableUnits L`, only for the binary Leavitt algebra.
* `KOne/ClassicalKOne.lean` has `BinaryLeavittClassicalK1`, the direct-limit
  quotient, again only for the binary Leavitt algebra — it could not be stated
  for a general ring because `elementaryColim` was known to be normal only there,
  and known for the trivial reason that it is everything.
* `Analysis/CStarKOne.lean` has `KOne A`, the *operator* `K₁` of a C⋆-algebra.
  Unrelated: that one is built from unitaries and homotopy, this one from
  invertible matrices and elementary generation.

`AlgebraicKOne (BinaryLeavittAlgebra k)` is `BinaryLeavittClassicalK1 k` by
definition, so `binaryLeavittClassicalK1_subsingleton` already says
`K₁(L_k(1,2)) = 0` in the vocabulary introduced here.

## Universes

Everything is stated for `R : Type*`; the manuscript's consumers instantiate at
`Type`, matching `MFQuotientUnits.lean`.
-/

namespace GroupApproximation
namespace AlgebraicK

open scoped commutatorElement

/-! ### The group -/

/-- **`K₁(R) = GL(R)/EL(R)`**, the printed definition, for an arbitrary unital
ring.

An `abbrev` so that the quotient's group structure, and the instances below, are
found through it. -/
noncomputable abbrev AlgebraicKOne (R : Type*) [Ring R] : Type _ :=
  ClassicalGLColim R ⧸ elementaryColim R

variable (R : Type*) [Ring R]

/-- **`K₁(R)` is abelian.**  Immediate from Whitehead's lemma: a quotient by a
normal subgroup is commutative exactly when that subgroup contains the
commutator subgroup, and `StableWhitehead.commutator_le_elementaryColim` says it
does. -/
noncomputable instance algebraicKOneCommGroup : CommGroup (AlgebraicKOne R) :=
  { (inferInstance : Group (AlgebraicKOne R)) with
    mul_comm := fun x y =>
      (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
        (StableWhitehead.commutator_le_elementaryColim R)).is_comm.comm x y }

/-- A class of `K₁(R)` is trivial exactly when its representative is stably
elementary. -/
theorem mk_eq_one_iff (x : ClassicalGLColim R) :
    (QuotientGroup.mk x : AlgebraicKOne R) = 1 ↔ x ∈ elementaryColim R :=
  QuotientGroup.eq_one_iff x

/-! ### The canonical map `κ : Rˣ → K₁(R)` -/

/-- `Rˣ ≅ GL₁(R)`, as the scalar embedding on units. -/
noncomputable def unitsToGLOne : Rˣ →* (Matrix (Fin 1) (Fin 1) R)ˣ :=
  Units.map (Matrix.scalar (Fin 1) : R →+* Matrix (Fin 1) (Fin 1) R).toMonoidHom

/-- **The printed `κ : R^× → K_1(R)`**: a unit of `R` is a `1 × 1` invertible
matrix, which names a class in the stable general linear group, which names a
class in `K₁(R)`. -/
noncomputable def kappa : Rˣ →* AlgebraicKOne R :=
  (QuotientGroup.mk' (elementaryColim R)).comp
    ((glColimOf R 1).comp (unitsToGLOne R))

theorem kappa_apply (u : Rˣ) :
    kappa R u = QuotientGroup.mk (glColimOf R 1 (unitsToGLOne R u)) := rfl

/-- `κ u = 1` exactly when the `1 × 1` matrix of `u` is stably elementary. -/
theorem kappa_eq_one_iff (u : Rˣ) :
    kappa R u = 1 ↔ glColimOf R 1 (unitsToGLOne R u) ∈ elementaryColim R :=
  mk_eq_one_iff R _

/-! ### Countability -/

/-- **The stable general linear group of a countable ring is countable.**  Every
class is represented at some finite rank, so the sigma type of all ranks
surjects onto it.

The two countability facts are `Algebra/CountableMatrixUnits.lean`'s; before
that module the tree re-derived them inline in five places, because the oldest
copy (`Leavitt/FamilyRankFour.lean`) is `private`. -/
instance classicalGLColim_countable [Countable R] : Countable (ClassicalGLColim R) := by
  haveI hunits : ∀ n : ℕ, Countable ((Matrix (Fin n) (Fin n) R)ˣ) := fun n =>
    CountableMatrixUnits.countable_matrix_units n
  have hsurj : Function.Surjective
      (fun p : Σ n : ℕ, (Matrix (Fin n) (Fin n) R)ˣ =>
        (⟦p⟧ : ClassicalGLColim R)) := by
    intro z
    obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (f := glStab R) z
    exact ⟨⟨i, x⟩, rfl⟩
  exact hsurj.countable

/-- **`K₁(R)` is countable when `R` is**, the second adjective the printed proof
uses. -/
instance algebraicKOne_countable [Countable R] : Countable (AlgebraicKOne R) :=
  QuotientGroup.mk_surjective.countable

end AlgebraicK
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AlgebraicK.algebraicKOneCommGroup
#audit_axioms GroupApproximation.AlgebraicK.kappa
#audit_axioms GroupApproximation.AlgebraicK.kappa_eq_one_iff
#audit_axioms GroupApproximation.AlgebraicK.classicalGLColim_countable
#audit_axioms GroupApproximation.AlgebraicK.algebraicKOne_countable
