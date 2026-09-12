import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Countable.Basic

/-!
# Countability of the two constructions the corpus quotients by

Two countability facts are needed by essentially every module that forms a
quotient of a countable group, and both were previously mirrored as a
`local instance` in each module that needed them.  Mathlib has neither: its
`Quotient.countable` is stated for `Quot r`, whose discrimination-tree key is
not the `HasQuotient.Quotient` of the `G ⧸ N` notation, so instance search
does not find it on its own even though the two are definitionally equal and
the term elaborates when written out.

This module states each fact once.  Neither is declared `instance` here: a
consumer opts in with

```
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable
```

which is exactly the scope the mirrored copies had, so nothing outside a module
that asks for it sees a new instance.

`quotientCountable` is stated without a normality hypothesis.  `G ⧸ N` is the
quotient by the left-coset relation whether or not `N` is normal, so the
surjection `G → G ⧸ N` needs no normality, and the copies that carried
`[N.Normal]` were carrying it only because they proved the statement through
`QuotientGroup.mk'_surjective`, whose group-homomorphism packaging does need it.
-/

namespace GroupApproximation
namespace CountableInstances

/-- A quotient of a countable group is countable. -/
theorem quotientCountable {G : Type*} [Group G] (N : Subgroup G) [Countable G] :
    Countable (G ⧸ N) :=
  Quotient.countable

/-- `Multiplicative ℤ` is countable, being `ℤ` carrying a different operation. -/
theorem multiplicativeIntCountable : Countable (Multiplicative ℤ) :=
  Countable.of_equiv ℤ Multiplicative.toAdd

end CountableInstances
end GroupApproximation
