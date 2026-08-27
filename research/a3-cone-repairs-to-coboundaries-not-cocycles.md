---
rg: 2
id: a3-cone-repairs-to-coboundaries-not-cocycles
kind: claim
title: The A_3 metric cone measures distance to coboundaries, not to cocycles
invalidates:
  - random-complex-stability-via-a3-cone
distinct_from:
  random-complex-linear-cocycle-stability: that is the open probabilistic estimate about random Linial--Meshulam complexes; this is a structural statement about what the repository's building-theoretic gadget can measure, and it holds on the fixed complex A_3(F_q) with no randomness in it
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
  - notes/TRUE_A3_METRIC_CONE_SYNCHRONIZATION.md
  - notes/TRUE_AUXILIARY_CONE_RADICAL_WITNESS_NO_GO.md
---

This repository's dimension-free synchronization theorem
(`notes/TRUE_A3_METRIC_CONE_SYNCHRONIZATION.md`) gauges any `Λ`-valued edge
connection `φ` on the spherical building `A_3(F_q)` so that

```text
||a·φ||_(L^r(E)) <= 9 ||K_φ||_(L^r(T)),
```

with the constant independent of `q`, of the conjugation-invariant subadditive
length, and of the representation dimension — in particular the same `9` for
`U(d)` with the normalized Hilbert--Schmidt length and for `Sym(d)` with
normalized Hamming distance.

The claim: this is an estimate of distance to `B^1`, the coboundaries.  The
building's cone is simply connected, so a connection with small curvature is
repaired to a **pure gauge**, and the repair necessarily destroys global
holonomy.  It is therefore not an estimate of distance to `Z^1`, the genuine
cocycles, on a complex whose fundamental group is nontrivial — where a
nontrivial cocycle is exactly a flat connection with nontrivial holonomy, the
data such a repair erases.

## Why the distinction is the whole difficulty

Chapman--Peled's route to a non-sofic hyperbolic group needs a cocycle
stability rate on random Linial--Meshulam complexes in the middle density
range, i.e. control of distance to `Z^1` on complexes whose fundamental group
is deliberately nontrivial, with expansion of connected covers doing the
global work.  A local repair that always lands in `B^1` cannot supply it: on
those complexes the two targets differ by precisely the representation data
the theorem is supposed to detect.

This repository already recorded the same obstruction in another language.
`notes/TRUE_AUXILIARY_CONE_RADICAL_WITNESS_NO_GO.md` shows that when radical
membership forces the encoded paths closed on `1-o(1)` of the finite base, a
bounded metric cone controls their holonomy by curvature and the marked
holonomy dies.  There the casualty was a sofic-radical witness; here it is the
`Z^1`-versus-`B^1` gap.  Same mechanism, and it is the mechanism, not a
limitation of the write-up.

## What the gadget is still good for

Everything local: it is a genuine dimension-free metric synchronization
theorem and a nonlinear circle-repair theorem on these buildings, and it
removes the spurious `d/2` fixity loss that appears if one converts from the
support norm to Hamming distance after applying the published Dinur--Meshulam
statement.  Nothing above weakens that.
