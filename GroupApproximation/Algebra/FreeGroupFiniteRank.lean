import GroupApproximation.Algebra.ReidemeisterSchreier
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.Data.ZMod.Basic

/-!
# A finitely generated free group has finite rank

`Algebra/ReidemeisterSchreier.lean` reduces "finite presentation passes to
finite-index subgroups" to exactly one input,
`FiniteIndex.FreeFiniteIndexFinitelyPresented`: a finite-index subgroup of a
finitely generated free group is finitely presented.  This module proves that
input, so the reduction becomes a theorem.

Two halves were already available and neither is the obstruction:

* Nielsen--Schreier — a subgroup of a free group is free — is Mathlib's
  `subgroupIsFreeOfIsFree`, and it is an instance;
* a finite-index subgroup of a finitely generated group is finitely generated
  is `FiniteIndex.group_fg_of_finiteIndex` (`Algebra/SchreierGenerators.lean`).

What was missing is the passage between them: "free and finitely generated" to
"free on a *finite* basis".  Classically one quotes Schreier's index formula
`rank = 1 + [F:P](n-1)`, which Mathlib does not have.  It is not needed — only
finiteness of the basis is, and that follows from finite generation alone.

## The argument

`finite_of_fg_freeGroup` avoids both the index formula and the abelianization.
Let `M` be any finite nontrivial group and let `S` be a finite generating set of
`FreeGroup α`.  Restricting `FreeGroup.lift` to `S`,

```
    (α → M)  →  (↥S → M),      f ↦ (s ↦ lift f s)
```

is injective, because two homomorphisms agreeing on a generating set are equal
and `FreeGroup.lift` is an equivalence.  The target is finite, so `α → M` is
finite; and `α` embeds in `α → M` by `a ↦ Pi.mulSingle a m` for any `m ≠ 1`, so
`α` is finite.  The counting content is the familiar `2^|α| ≤ 2^|S|`, but no
cardinal arithmetic is needed to say it this way.
-/

namespace GroupApproximation
namespace FiniteIndex

/-- **A finitely generated free group has a finite basis.**

The proof is a counting argument phrased as two injections: homomorphisms out of
`FreeGroup α` into a fixed finite group are determined by their values on a
finite generating set, and a basis element is recovered from the corresponding
`Pi.mulSingle`. -/
theorem finite_of_fg_freeGroup {α : Type*} (h : Group.FG (FreeGroup α)) :
    Finite α := by
  classical
  obtain ⟨S, hSclosure, hSfin⟩ := Group.fg_iff.mp h
  haveI : Finite S := hSfin.to_subtype
  -- Restriction to `S` is injective on maps `α → M`, for `M` any group.
  have hinj : Function.Injective
      (fun f : α → Multiplicative (ZMod 2) =>
        fun s : ↥S => FreeGroup.lift f (s : FreeGroup α)) := by
    intro f g hfg
    apply FreeGroup.lift.injective
    refine MonoidHom.eq_of_eqOn_dense hSclosure ?_
    intro x hx
    exact congrFun hfg ⟨x, hx⟩
  haveI : Finite (α → Multiplicative (ZMod 2)) := Finite.of_injective _ hinj
  -- A nontrivial value turns `Pi.mulSingle` into an embedding of the index type.
  obtain ⟨m, hm⟩ := exists_ne (1 : Multiplicative (ZMod 2))
  refine Finite.of_injective
    (fun a : α => (Pi.mulSingle a m : α → Multiplicative (ZMod 2))) ?_
  intro a b hab
  by_contra hne
  have h1 := congrFun hab a
  simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne] at h1
  exact hm h1

/-- **The Reidemeister--Schreier input, discharged.**  A finite-index subgroup
of a finitely generated free group is finitely presented.

Nielsen--Schreier makes the subgroup free, Schreier makes it finitely generated,
and `finite_of_fg_freeGroup` makes its basis finite; a free group on a finite
basis is finitely presented by Mathlib's instance. -/
theorem freeFiniteIndexFinitelyPresented : FreeFiniteIndexFinitelyPresented := by
  intro n P hP
  haveI : P.FiniteIndex := hP
  haveI : Group.FG ↥P := group_fg_of_finiteIndex P
  haveI : Finite (IsFreeGroup.Generators ↥P) :=
    finite_of_fg_freeGroup
      (Group.fg_of_surjective
        (f := (IsFreeGroup.toFreeGroup (G := ↥P)).toMonoidHom)
        (IsFreeGroup.toFreeGroup (G := ↥P)).surjective)
  exact Group.IsFinitelyPresented.equiv (IsFreeGroup.toFreeGroup (G := ↥P)).symm

/-- **Finite presentation passes to finite-index subgroups**, with no remaining
input.  Compare `finitePresentationFiniteIndexPermanence_of_freeInput` in
`Kazhdan/LatticeRouteRemainder.lean`, which takes the free case as a
hypothesis. -/
theorem isFinitelyPresented_subgroup_of_finiteIndex' {Γ : Type} [Group Γ]
    (Λ : Subgroup Γ) [Λ.FiniteIndex] (hΓ : Group.IsFinitelyPresented Γ) :
    Group.IsFinitelyPresented ↥Λ :=
  isFinitelyPresented_subgroup_of_finiteIndex freeFiniteIndexFinitelyPresented Λ hΓ

end FiniteIndex
end GroupApproximation
