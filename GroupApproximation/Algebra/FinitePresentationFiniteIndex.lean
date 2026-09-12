import GroupApproximation.Algebra.SteinbergSL3
import GroupApproximation.Algebra.FreeGroupFiniteRank
import Mathlib.Data.ZMod.Basic

/-!
# Finite presentation of the congruence subgroups of `SL₃(ℤ)`

`Kazhdan/TorsionFreeKazhdanPartner.lean` once listed `gamma3_finitelyPresented`
as an open leaf of the partner workstream, "in two halves: a finite presentation
of `SL₃(ℤ)` … and Reidemeister--Schreier descent of finite presentation to a
finite-index subgroup".  Both halves are theorems, and so is everything below:
no statement in this module carries a hypothesis.

* The `SL₃(ℤ)` half is `Algebra/SteinbergSL3.lean`, itself only a restatement:
  the thirteen-relator presentation is Milnor's Corollary 10.3 presentation of
  `SL₃(ℤ)`, and it is complete (`P13DescentMaster.p13CompletenessEquiv`).
* The descent half is `Algebra/ReidemeisterSchreier.lean`, which proves
  `isFinitelyPresented_subgroup_of_finiteIndex` outright — the rewriting
  theorem, finiteness of the transversal conjugates, and the assembly — together
  with `Algebra/FreeGroupFiniteRank.lean`, which discharges the one general fact
  about free groups that assembly left as an input.

## The input that used to be open

`FiniteIndex.FreeFiniteIndexFinitelyPresented` says a finite-index subgroup of a
finitely generated free group is finitely presented.  Mathlib supplies
Nielsen--Schreier — such a subgroup is free — but not the *rank*: Schreier's
index formula `rank = 1 + [F:P](n-1)` is absent at this revision.  It is not
needed.  `FreeGroupFiniteRank.finite_of_fg_freeGroup` shows a finitely generated
free group has a finite basis directly, by a counting argument, and
`FreeGroupFiniteRank.freeFiniteIndexFinitelyPresented` is the resulting theorem.
This module therefore uses `isFinitelyPresented_subgroup_of_finiteIndex'`, the
form with no remaining input.

## Why the partner module is not imported

`Kazhdan/TorsionFreeKazhdanPartner.lean` imports *this* module, so importing it
back would be a cycle.  The statements below are phrased on the reduction map
itself, which needs no import and is more general — every level `m` at once.  At
`m = 3`, `(Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))).ker` is
`CongruenceSubgroup.gamma3` by definition, so
`isFinitelyPresented_congruenceSubgroup` discharges `gamma3_finitelyPresented`
there by `exact`, with no bridge lemma and no hypothesis.
-/

namespace GroupApproximation
namespace FiniteIndex

/-- **Every finite-index subgroup of `SL₃(ℤ)` is finitely presented.**
`SL₃(ℤ)` is finitely presented by `SteinbergSL3`, and finite presentation
descends along a finite-index inclusion by Reidemeister--Schreier. -/
theorem isFinitelyPresented_finiteIndex_SL3
    (Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) [Λ.FiniteIndex] :
    Group.IsFinitelyPresented ↥Λ :=
  isFinitelyPresented_subgroup_of_finiteIndex' Λ
    SteinbergSL3.isFinitelyPresented_specialLinearGroup

/-- **The principal congruence subgroup `Γ(m)` has finite index**, for every
positive level: it is the kernel of entrywise reduction into a finite group. -/
instance finiteIndex_congruenceSubgroup (m : ℕ) [NeZero m] :
    (Matrix.SpecialLinearGroup.map (n := Fin 3) (Int.castRingHom (ZMod m))).ker.FiniteIndex :=
  Subgroup.finiteIndex_ker _

/-- **`Γ(m)` is finitely presented**, for every positive level, with no
hypotheses.

At `m = 3` this is `CongruenceSubgroup.gamma3` on the nose — that subgroup is
defined as `reduceMod3.ker` with `reduceMod3` the same `SpecialLinearGroup.map`
— so this theorem is the drop-in for `gamma3_finitelyPresented`.  The finite
index is not an extra hypothesis there either: `finiteIndex_gamma3` is already
proved, from finiteness of `SL₃(ℤ/3)` alone, with no surjectivity of the
reduction map. -/
theorem isFinitelyPresented_congruenceSubgroup (m : ℕ) [NeZero m] :
    Group.IsFinitelyPresented
      ↥(Matrix.SpecialLinearGroup.map (n := Fin 3) (Int.castRingHom (ZMod m))).ker :=
  isFinitelyPresented_finiteIndex_SL3 _

end FiniteIndex
end GroupApproximation
