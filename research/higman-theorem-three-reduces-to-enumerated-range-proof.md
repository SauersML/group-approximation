---
rg: 2
id: higman-theorem-three-reduces-to-enumerated-range-proof
kind: route
title: Split off the empty case, enumerate the rest, and take a computable union
target: higman-theorem-three-reduces-to-enumerated-range
requires: []
artifacts:
  - GroupApproximation/Higman/TheoremThreeAssembly.lean
  - GroupApproximation/Higman/GeneratedEnumeration.lean
---

Machine-checked.

Given a recursively enumerable `B`, either `B` is empty --- and
`higmanGenerated_empty` applies --- or it is nonempty, and
`exists_computable_enumeration` produces a total computable `c` whose range of
decoded codes is exactly `B`.  `EnumeratedRangeGenerated` at that `c` gives
`HigmanGenerated B`, which is `higmanGenerated_of_REset`; packaging it as the
structure field is `higmanTheoremThree_of_enumeratedRange`.

`statement_of_four_enumerated` is then the same composite as
`statement_of_four` with the second argument replaced.

## Why the empty case is not a technicality

`exists_computable_enumeration` is Higman's Lemma 2.8 *with the hypothesis his
printed statement omits*.  A total computable `c : N -> List (Z x Z)` has a
nonempty range by definition, so no such `c` enumerates the empty set; the
printed lemma therefore fails at `X = empty`.  Restoring `B.Nonempty` and
proving the empty case separately is what makes the split above exhaustive, and
it is the reason `higmanGenerated_empty` had to exist at all.

## What a proof of the residual looks like

It is the step Higman's Section 2 spends its length on: exhibiting the range of
a computable enumeration as a value of the `omega` operation over sets built by
finite unions.  Nothing in the current tree attempts it, and it is stated over
`Computable c` rather than over an abstract RE predicate precisely so that the
attempt has an explicit object to induct on.
