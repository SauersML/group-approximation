---
rg: 2
id: nonempty-tower-classes-yield-computable-towers
kind: claim
title: Over an infinite finitely presented group with solvable word problem, if some computable datum has a nonempty margin covering tower class, then some computable datum has a tower class with a computable member
distinct_from:
  free-minimal-subshifts-with-computable-moduli-exist: that is the non-effective existence statement (N), equivalent to nonemptiness of some tower class; this is the path-selection step from (N) to a computable tower, and asserts nothing about existence.
  tower-classes-are-computably-bounded-pi01-classes: that ESTABLISHES that tower classes are computably bounded Pi01 classes and relates them to (N) and (M2); this is the OPEN basis step between the two.
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2); this is the implication (N) => (M2), which together with (N) gives (M2).
---

**OPEN.** The path-selection premise of route
`effective-minimal-free-subshifts-via-tower-class-basis`.

**Statement.** Let `Λ` be an infinite finitely presented group with solvable
word problem. Suppose `T_D ≠ ∅` for some computable datum `D`, in the notation
of `tower-classes-are-computably-bounded-pi01-classes`. Then `T_{D'}` has a
computable member for some computable datum `D'`, which may differ from `D`.

**Why it is a separate premise.**
- *It is not a formal consequence of nonemptiness.* Each `T_D` is a computably
  bounded Π⁰₁ class, and such classes can be nonempty with no computable member
  (context only).
- *The freedom to change data matters.* `D'` may enlarge the alphabet and
  loosen the bounds. So a proof may pass from a noncomputable tower to a coarser
  computable one, for example by a factor map or by recoding.
- *By `tower-classes-are-computably-bounded-pi01-classes`, part 4:*
  - the statement is equivalent to "(N) ⇒ (M2)" for `Λ`;
  - together with (N) it gives (M2).
- *It can fail independently of (N).* It fails for `Λ` exactly when (N) holds
  for `Λ` but `Λ` carries no nonempty effectively closed minimal free subshift.
  Nothing known rules this out.

**Evidence.**
- *For `Z^d` and products of such groups* it holds, because (M2) holds there.
- *Methods that cannot prove it.* A method that only shows the tree of some
  `T_D` is infinite does not decide it. That includes Zorn, compactness limits,
  the local lemma plus compactness, and genericity.

## Attempts

None beyond the evidence above.
