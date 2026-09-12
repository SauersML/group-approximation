---
rg: 2
id: steinberg-flag-injectivity-via-chord-recurrence
kind: route
title: Prove flag-incidence injectivity from the three-coordinate chord recurrence
target: steinberg-flag-fox-map-is-injective
requires:
  - steinberg-cycles-have-big-cell-chord-coordinates
  - steinberg-fox-chord-actions-are-explicit
  - steinberg-chord-fox-recurrence-has-zero-solutions
---

Let `F in ker D_p`.  By `(SFI4)`, `F` is a Steinberg cycle killed by `X,Y`.
Set `f=R_pF`.  Equations `(SBC4)--(SBC5)` say that `f` satisfies both chord
recurrences.  The second prerequisite gives `f=0`, and the isomorphism
`(SBC3)` then gives `F=E_pf=0`.  Thus `D_p` is injective.
