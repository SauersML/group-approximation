---
rg: 2
id: central-extension-twisted-sector-criterion
kind: claim
title: MF of a central order-two extension is the twisted sector over the quotient
distinct_from:
  mf-extension-nonclosure: That claim exhibits an extension with MF kernel and quotient whose total group is not MF; this one is an exact criterion for central order-two kernels, in which the missing datum is named as a twisted asymptotic model.
  central-sign-corona-obstruction: That claim proves the central involution dies in every corona model for the Kazhdan compression pattern; this one is a general reformulation of MF for any central order-two extension, with no Kazhdan hypothesis.
  thom-central-corner-criterion: That is the published tracial analogue — hyperlinearity of a central extension as embeddability of every twisted corner into `R^omega`, and it comes with descent to central quotients; this is the operator-norm corona version for an order-two kernel, and MF has no descent, which is exactly why the quotient claims here are not free.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
  - notes/NOTEPAD.md
---

Let `1 -> C_2 -> G -> K -> 1` be central with `K` MF, let
`s(k)s(l) = omega(k,l) s(kl)` be a section cocycle, and let `chi` be the
nontrivial character of `C_2`.  Then `G` is MF if and only if there are maps
`v_n : K -> U(d_n)` with

```text
|| v_n(k) v_n(l) - chi(omega(k,l)) v_n(kl) ||_op -> 0
```

for every fixed pair `k,l`.  No separation condition on `v_n` is needed.

**What this says about the two marked quotients, and what it does not.**
Applied to `(E, <w>)` or `(W, <zeta>)`, the twisted condition says exactly
that some corona representation of the total group sends the central
involution to `-1`, which Theorem A refutes.  So here the criterion is a
restatement of the non-MF theorem — the failure of MF for `E` is precisely
the emptiness of the twisted sector over `E/<w>` — and it is consistent with
either answer for `commuting-lamp-quotient-mf` and
`literal-mark-quotient-mf`: MF of the quotient is a hypothesis of the useful
direction, not a conclusion.  It is **not** an obstruction to either claim.

The contrast with the tracial world is the point.  Thom's Remark 3.4
(`thom-central-corner-criterion`) gives descent — a central quotient of a
hyperlinear group is hyperlinear — so the analogous questions there are
automatic.  MF has no descent (`mf-quotient-nonclosure`), and that missing
descent is exactly the content of the two open quotient claims.
