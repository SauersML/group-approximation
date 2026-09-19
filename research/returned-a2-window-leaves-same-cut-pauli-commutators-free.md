---
rg: 2
id: returned-a2-window-leaves-same-cut-pauli-commutators-free
kind: claim
title: The returned A2 window leaves both same-cut Pauli commutators free
invalidates:
  - returned-a2-window-authenticates-same-v-pauli-rows
distinct_from:
  returned-opposite-cross-zero-has-finite-s6-model: that gives the finite returned Coxeter model but does not test a Pauli pair on one invariant positive cut; this adjoins the packet locally and computes both commutator defects exactly.
  relative-a2-weyl-orbit-has-seven-state-gauge-model: that moves one controlled packet through fresh reservoir supports before return; this gives a finite group model with a central word-visible common cut and two simultaneous Pauli tests.
  returned-boolean-coefficient-window-has-finite-marked-model: that fences the entire Boolean coefficient group but does not exhibit a common positive Pauli cut on which both commutators stay macroscopically nonzero; this supplies that exact joint witness.
---

**ESTABLISHED EXACT SAME-CUT FENCE.**  The returned `A_2` reverse-product
window, its literal order-three relative word, and packet-local Pauli
relations do not imply either of the two mixed Pauli commutator rows needed
by `relative-gauge-invariance-transfers-cross-orthogonality`.

More precisely, there is a finite group model with a literal relative word
`V`, a central `V`-invariant projection `E` of normalized trace `1/8`, and
involutions `X,Z` such that on `E`

```text
XZ=-ZX,
||[V,X]E||_(2,E)^2=||[V,Z]E||_(2,E)^2=2.              (RPF1)
```

Here `||.||_(2,E)` is normalized by the corner trace.  Every child and
parent reverse-product Whitehead row, both returned opposite cross-zero
comparisons, the full three-step relative orbit, and all packet-local Pauli
relations are exact in this model.

Consequently no bounded normal-closure filling in the currently named
returned-window relations can produce `[V,X]=1` or `[V,Z]=1` on the common
cut.  In fact the conclusion is stronger: neither equality is any group-
theoretic consequence of that finite window.  The missing inventory item is
therefore an actual mixed occurrence relation identifying at least one
returned Pauli occurrence with its source occurrence, or a finite-coordinate
rank/boundary statement which quantitatively charges their difference.

The claim is deliberately scoped.  A new payload-coupled relation can
exclude the finite model below; this result does not say that no such row
exists in a larger presentation.  It says that relative order, braid,
cross-zero, return, and packet-local Pauli data do not authenticate it.

DERIVATION
returned-a2-same-cut-pauli-free-proof
