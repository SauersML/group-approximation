---
rg: 2
id: nonhyperlinear-via-deligne-central-mark-collapse
kind: route
title: One-word HS collapse in Deligne's triple cover gives an explicit non-hyperlinear group
target: non-hyperlinear-group
requires:
  - deligne-triple-cover-fd-central-invisibility
  - deligne-central-mark-hs-collapse
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
---

Let `E_3` and its nontrivial central element `z` be as in
`deligne-triple-cover-fd-central-invisibility`.  Suppose `E_3` were
hyperlinear.  Canonical group-trace microstates on larger and larger finite
word balls have presentation defects tending to zero and keep the nonidentity
word `z` separated from the identity; for example their normalized traces on
`z` tend to zero, so

```text
||phi_n(z)-I||_2^2 -> 2.                                 (NDM1)
```

But `deligne-central-mark-hs-collapse` applied to the same microstates gives
`||phi_n(z)-I||_2->0`, contradicting `(NDM1)`.  Hence the explicit finitely
presented group `E_3` is not hyperlinear.

The route needs no full HS stability theorem and no construction of a nearby
exact representation: collapse of this one word is sufficient.
