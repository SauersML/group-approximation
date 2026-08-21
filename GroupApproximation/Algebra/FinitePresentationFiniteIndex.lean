import GroupApproximation.Algebra.SteinbergSL3
import GroupApproximation.Algebra.ReidemeisterSchreier
import Mathlib.Data.ZMod.Basic

/-!
# Finite presentation of the congruence subgroups of `SL₃(ℤ)`

`Kazhdan/TorsionFreeKazhdanPartner.lean` lists `gamma3_finitelyPresented` as an
open leaf of the partner workstream, "in two halves: a finite presentation of
`SL₃(ℤ)` … and Reidemeister--Schreier descent of finite presentation to a
finite-index subgroup".  Both halves already exist.

* The `SL₃(ℤ)` half is `Algebra/SteinbergSL3.lean`, itself only a restatement:
  the thirteen-relator presentation is complete
  (`P13DescentMaster.p13CompletenessEquiv`), incomplete-proof-free.
* The descent half is `Algebra/ReidemeisterSchreier.lean`, which proves
  `isFinitelyPresented_subgroup_of_finiteIndex` outright — the rewriting
  theorem, finiteness of the transversal conjugates, and the assembly.

So the leaf is not open.  It reduces to **one** general fact about free groups,
`FiniteIndex.FreeFiniteIndexFinitelyPresented`, and this module performs that
reduction and nothing else.

## The one remaining input

`FreeFiniteIndexFinitelyPresented` says a finite-index subgroup of a finitely
generated free group is finitely presented.  Mathlib supplies Nielsen--Schreier
— such a subgroup is free — but not the *rank*: Schreier's index formula
`rank = 1 + [F:P](n-1)` is absent at this revision, and "free and finitely
generated" does not reduce to "free on a finite basis" without an argument
Mathlib also lacks.  `Algebra/SchreierGenerators.lean` proves the generation
half (`group_fg_of_finiteIndex`), so what is missing is exactly the passage
from a finitely generated free group to a finite basis.

Nothing here assumes it.  Every statement below takes it as an explicit
hypothesis, in the style of `Kazhdan/LatticeRouteRemainder.lean`.

## Why the partner module is not imported

`Kazhdan/TorsionFreeKazhdanPartner.lean` still carries open leaves on its
torsion-freeness leaf, and the library compiles with `-DwarningAsError=true`,
under which an incomplete declaration is a build failure.  Importing it would
therefore make this module unbuildable.  The statements below are phrased on
the reduction map itself so that no import is needed: at `m = 3`,
`(Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))).ker` is
`CongruenceSubgroup.gamma3` by definition, so
`isFinitelyPresented_congruenceSubgroup` discharges `gamma3_finitelyPresented`
there by `exact` once that module is incomplete-proof-free.
-/

namespace GroupApproximation
namespace FiniteIndex

/-- **Every finite-index subgroup of `SL₃(ℤ)` is finitely presented**, given the
free-group input.  `SL₃(ℤ)` is finitely presented by `SteinbergSL3`, and finite
presentation descends along a finite-index inclusion by
Reidemeister--Schreier. -/
theorem isFinitelyPresented_finiteIndex_SL3
    (hfree : FreeFiniteIndexFinitelyPresented)
    (Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) [Λ.FiniteIndex] :
    Group.IsFinitelyPresented ↥Λ :=
  isFinitelyPresented_subgroup_of_finiteIndex hfree Λ
    SteinbergSL3.isFinitelyPresented_specialLinearGroup

/-- **The principal congruence subgroup `Γ(m)` has finite index**, for every
positive level: it is the kernel of entrywise reduction into a finite group. -/
instance finiteIndex_congruenceSubgroup (m : ℕ) [NeZero m] :
    (Matrix.SpecialLinearGroup.map (n := Fin 3) (Int.castRingHom (ZMod m))).ker.FiniteIndex :=
  Subgroup.finiteIndex_ker _

/-- **`Γ(m)` is finitely presented**, for every positive level, given the
free-group input.

At `m = 3` this is `CongruenceSubgroup.gamma3` on the nose — that subgroup is
defined as `reduceMod3.ker` with `reduceMod3` the same `SpecialLinearGroup.map`
— so this theorem is the intended drop-in for the sorried
`gamma3_finitelyPresented`.  The finite index is not an extra hypothesis there
either: `finiteIndex_gamma3` is already proved, from finiteness of `SL₃(ℤ/3)`
alone, with no surjectivity of the reduction map. -/
theorem isFinitelyPresented_congruenceSubgroup
    (hfree : FreeFiniteIndexFinitelyPresented) (m : ℕ) [NeZero m] :
    Group.IsFinitelyPresented
      ↥(Matrix.SpecialLinearGroup.map (n := Fin 3) (Int.castRingHom (ZMod m))).ker :=
  isFinitelyPresented_finiteIndex_SL3 hfree _

end FiniteIndex
end GroupApproximation
