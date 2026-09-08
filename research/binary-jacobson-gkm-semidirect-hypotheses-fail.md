---
rg: 2
id: binary-jacobson-gkm-semidirect-hypotheses-fail
kind: claim
title: The published semidirect-product extension theorem does not reach the Jacobson symbol sequence
distinct_from:
  marked-graph-action-not-residually-finite: that refutes Definition 2.6 of the same paper for the Kun--Thom invariant graphs, so the graph-wreath theorems are unavailable there; this checks Theorem 1.1 of that paper against a different group in a different lane, and the hypothesis that fails is finite generation and residual finiteness of an amenable kernel rather than residual finiteness of an action.
  binary-jacobson-mf-radical-dichotomy: that computes the two-valued MF-radical alternative for the elementary group; this rules out one named published route to the MF side of that alternative, and computes nothing.
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that establishes the symbol sequence and the finite-quotient collapse; this consumes that sequence as input and tests one external theorem against it.
artifacts:
  - research/artifacts/gkm-extension-theorem-vs-jacobson-kernel-2026-09-08.md
---

**ESTABLISHED.**  Theorem 1.1 of Gao--Kunnawalkam Elayavalli--Mj,
`arXiv:2607.29571v1`, reads

```text
G finitely generated residually finite amenable,
L exact MF/PMF/PFF                  ==>   G x| L is MF/PMF/PFF.       (GKM1)
```

It does not apply to the Jacobson symbol sequence of
`binary-jacobson-elementary-mark-is-finite-quotient-invisible`,

```text
1 -> L_J -> E -> Q_0 -> 1,
E = EL_5(J),   L_J = GL_fin(N x {1,...,5},F_2),   Q_0 = EL_5(F_2[z,z^-1]),
```

and the failure is on the kernel, in a way that no change of rank or basis
repairs.  Of the three hypotheses `(GKM1)` puts on its base:

```text
amenable            SATISFIED   (L_J is locally finite),
residually finite   FAILS       (L_J is infinite simple),
finitely generated  FAILS       (L_J is infinite locally finite).      (GKMJ1)
```

Both failures follow from `L_J` being *infinite simple locally finite*, which
is exactly what the symbol sequence supplies.  Separately, `(GKM1)` is a
statement about semidirect products and no splitting of the symbol sequence is
established; this claim asserts no obstruction to splitting, only that
applying `(GKM1)` would require a splitting nobody has proved.

The other side of `(GKM1)` is met and does not need re-checking: `Q_0` is a
finitely generated linear group, hence residually finite and MF, and finitely
generated linear groups are exact.

**Corollary, conditional.**  By `binary-jacobson-steinberg-head-root-is-mf-invisible`
we have `Rad_MF(E) = L_J != 1`, so `E` is not operator MF; `(GKM1)` concludes
MF of the total group.  Hence no theorem of that shape can apply here, and the
hypothesis failure `(GKMJ1)` is not incidental.  This corollary inherits that
node's property-(T) dependency -- `property-t-free-jacobson-head-collapse` is
the standing obligation to remove it -- whereas `(GKMJ1)` itself is an
unconditional inspection of the symbol sequence.

**What this does not do.**  It supplies no progress on the head root in either
direction.  Retaining the head is all-or-nothing by
`binary-jacobson-head-retaining-homomorphisms-are-faithful`, so there is no
partial MF target to aim an extension theorem at even where one applies.
