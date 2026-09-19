---
rg: 2
id: mf-antipodal-sign-corner-visibility
kind: claim
title: Antipodal elements are maximally visible in the sign corner of an MF group
distinct_from:
  mf-finite-normal-tracially-visible: That claim makes the elements of a finite normal subgroup visible; this one makes visible elements of infinite order lying far outside it, using a relation rather than finiteness.
  mf-invariant-corner-visibility: That open claim asks for a corner for an arbitrary element; this established one supplies the corner and the visibility whenever the group has a central involution and one antipodal relation.
artifacts:
  - GroupApproximation/Sofic/AntipodalTraceExtraction.lean
  - notes/TRUE_ANTIPODAL_TRACE_EXTRACTION.md
---

Let `G` be a countable MF group with a central involution `z != 1`, and let
`g in G` admit some `s in G` with

```text
s g s^(-1) = z g.                                                 (A1)
```

Then `g` is tracially visible with constant `1`: there are models with
multiplicative defect as small as desired on any prescribed finite set whose
normalized trace at `g` tends to `0`, i.e. `||model(g)-1||_(2,norm)^2 -> 2`.

The mechanism is that the sign corner of an MF model of `G` manufactures, for
free, exactly the antipodal conjugacy `S U S^* = -U` whose local
trace-extraction certificate `4|tr_d(U)|^2 <= ||S U S^* + U||_2^2` is already
formalized.  `notes/TRUE_ANTIPODAL_TRACE_EXTRACTION.md` states the open half as
"construct or recover, in compatible matrix coordinates, a unitary `S` and a
marked unitary `U` whose antipodal defect tends to zero"; for an MF group with
a central involution, `(A1)` is a sufficient group-theoretic condition.

Consequently an MF group with a central involution `z != 1` is hyperlinear as
soon as every nontrivial element is `z`-antipodal in the sense of `(A1)`, or
lies in a finite normal subgroup, or survives in some hyperlinear quotient.
