import GroupApproximation.Algebra.HyperbolicFreeGroup
import GroupApproximation.Kazhdan.SharpExistenceCertificateRoute
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# A concrete group satisfying four of `SharpExistence`'s five clauses

`Kazhdan/SharpExistenceCertificateRoute.lean` reduces `SharpExistence` to a
concrete group that is infinite, finitely presented, torsion-free and
hyperbolic, plus a rational Hodge certificate for property `(T)`.  Until
`Algebra/HyperbolicFreeGroup.lean` the library could not exhibit *any* group
meeting the first four clauses beyond the elementary examples --- the only
hyperbolic groups available were finite ones, the trivial group, and
`Multiplicative ℤ`, and `Multiplicative ℤ` is the one the module docstring of
`Kazhdan/TorsionFreeHyperbolicKazhdan.lean` already uses to show that property
`(T)` is the whole content.

A free group of finite rank meets all four, and this module records that:

* infinite --- `infinite_freeGroup`, from surjectivity of the reduced length;
* finitely presented --- Mathlib's instance for a finite basis;
* torsion-free --- Mathlib's `IsMulTorsionFree` instance, through
  `IsPowerTorsionFree.of_isMulTorsionFree`;
* hyperbolic --- `isHyperbolicGroup_freeGroup`, proved here at `δ = 0`.

`freeGroup_sharpProfile` is the four clauses together.

## And the fifth necessarily fails

`not_hasKazhdanPropertyT_freeGroup` proves it, and the proof says why the
failure is structural rather than accidental: a free group on a nonempty basis
surjects onto `Multiplicative ℤ`, property `(T)` passes to quotients
(`HasKazhdanPropertyT.of_surjective`), and the infinite cyclic group is not
Kazhdan (`not_hasKazhdanPropertyT_multiplicative_int`).

So a free group is not a witness and cannot be repaired into one.  What it
supplies is the machinery: `Hyperbolic.IsTreeLike` and its free-group
instantiation are the base case for the small-cancellation and Bass--Serre
arguments by which a genuine witness --- a torsion-free hyperbolic group with a
certificate --- would be proved hyperbolic.  Before this module that base case
did not exist.
-/

namespace GroupApproximation
namespace Hyperbolic

/-- **A free group on a nonempty basis is infinite.**  Reduced length is
surjective onto `ℕ`. -/
theorem infinite_freeGroup (α : Type) [DecidableEq α] [Nonempty α] :
    Infinite (FreeGroup α) :=
  Infinite.of_surjective FreeGroup.norm FreeGroup.norm_surjective

/-- **Four of the five clauses of `SharpExistence`, for a concrete group.**
Only property `(T)` is missing. -/
theorem freeGroup_sharpProfile (α : Type) [Fintype α] [DecidableEq α]
    [Nonempty α] :
    Infinite (FreeGroup α) ∧ Group.IsFinitelyPresented (FreeGroup α) ∧
      IsPowerTorsionFree (FreeGroup α) ∧ IsHyperbolicGroup (FreeGroup α) :=
  ⟨infinite_freeGroup α, inferInstance, IsPowerTorsionFree.of_isMulTorsionFree,
    isHyperbolicGroup_freeGroup α⟩

/-- **A free group is not Kazhdan.**  It surjects onto the infinite cyclic
group, property `(T)` passes to quotients, and the infinite cyclic group is not
Kazhdan.  So the fifth clause fails, and fails for a reason no repair can
remove. -/
theorem not_hasKazhdanPropertyT_freeGroup (α : Type) [DecidableEq α]
    [Nonempty α] : ¬ HasKazhdanPropertyT.{0, 0} (FreeGroup α) := by
  intro hT
  obtain ⟨a⟩ := ‹Nonempty α›
  set φ : FreeGroup α →* Multiplicative ℤ :=
    FreeGroup.lift (fun _ : α => Multiplicative.ofAdd (1 : ℤ)) with hφ
  have hof : φ (FreeGroup.of a) = Multiplicative.ofAdd (1 : ℤ) := by
    rw [hφ]
    simp
  have hsurj : Function.Surjective φ := by
    intro g
    refine ⟨FreeGroup.of a ^ (Multiplicative.toAdd g), ?_⟩
    rw [map_zpow, hof]
    apply Multiplicative.ext
    simp
  exact not_hasKazhdanPropertyT_multiplicative_int
    (HasKazhdanPropertyT.of_surjective φ hsurj hT)

/-- **The gap, stated as a single theorem.**  A free group of finite rank meets
every clause of `SharpExistence` except property `(T)`, and fails that one.
This is the exact sense in which the remaining work is a certificate for a
*different* group and not more hyperbolicity theory. -/
theorem freeGroup_sharpProfile_and_not_kazhdan (α : Type) [Fintype α]
    [DecidableEq α] [Nonempty α] :
    (Infinite (FreeGroup α) ∧ Group.IsFinitelyPresented (FreeGroup α) ∧
        IsPowerTorsionFree (FreeGroup α) ∧ IsHyperbolicGroup (FreeGroup α)) ∧
      ¬ HasKazhdanPropertyT.{0, 0} (FreeGroup α) :=
  ⟨freeGroup_sharpProfile α, not_hasKazhdanPropertyT_freeGroup α⟩

end Hyperbolic
end GroupApproximation
