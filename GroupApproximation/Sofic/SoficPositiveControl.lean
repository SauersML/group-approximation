import GroupApproximation.Sofic.SoficTransfer
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

/-!
# Positive control: the soficity definition is satisfiable

Before this control module, every use of `IsSofic` in the development was
negative.  It appears elsewhere as a
hypothesis to be refuted (`not_isSofic_of_not_isLEF`), as a hypothesis to be
transported (`SoficTransfer`), or as the conclusion of the two headline
theorems under a `¬`.  Before this module, nothing anywhere in the library
exhibited a single group satisfying `IsSofic`, and `SoficModel` was never once
constructed.

That is a gap in the same shape as a detector that has never been shown to
fire.  A scan that reports nothing is indistinguishable from a clean corpus
until a planted defect proves it can report something; likewise `¬ IsSofic G`
is indistinguishable from `IsSofic` being unsatisfiable -- a definition
accidentally so strong that no group at all meets it -- until some group is
shown to meet it.  Under an unsatisfiable definition every theorem in this
repository would still be true, every proof would still be kernel-checked, the
dependency audit would still be clean, and the result would be worth nothing.

The left regular representation proves every finite group sofic.  Cyclic
quotients give an exact local model of the infinite cyclic group
`Multiplicative ℤ`.  `scripts/Audit.lean` pins both controls alongside the
headline results, so neither can be deleted while the negative results remain.
-/

/-! ### Finite groups in an arbitrary universe

`FiniteModel` carries a `Type` and `regularModel` therefore models a group by
itself only in universe zero.  A finite group in any universe is still sofic:
enumerate it and use the left regular representation on the enumeration, a
group that does live in `Type`.  This is what lets a statement about an
arbitrary nonsofic group avoid carrying `Infinite` as a hypothesis. -/
