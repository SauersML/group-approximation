---
rg: 2
id: bcv-qr-cz-and-identity-gauges-remain-independent
kind: claim
title: The BCV Question-Reduction apparatus leaves CZ and identity multiplicity gauges independent
distinct_from:
  bcv-question-reduction-retains-readable-closure: that follows the explicit honest completeness strategy and transports readable closure; this audits every exact apparatus model before the Intro edge is used.
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that proves cancellation once the same gauge is available; this proves that BCV sampling, Pauli translation, and autoaccept anchors do not supply that equality.
  zpc-active-identity-copy-mixed-occurrence-on-a-positive-corner: that asks for a positive-corner occurrence theorem; this gives an exact finite-dimensional model with no such corner for the BCV-only candidate.
---

**ESTABLISHED NO-GO.** The sampling and hiding apparatus in BCV Question
Reduction, even at exact value one, does not force a CZ-outer answer
observable and an identity-outer answer observable to use the same
multiplicity gauge. This remains false after adjoining the automatically
accepting anchor vertices from combinatorial detyping.

More precisely, on the two-qubit Pauli label space and a two-dimensional
multiplicity space there is an exact apparatus model with

```text
T = C_Z tensor sigma_z,          A = I tensor sigma_x,       (BQA1)
```

where `T` normalizes the Pauli packet by the controlled-Z outer
automorphism and `A` has trivial outer action. All Pauli-basis,
SamZ--answer commutation, sidewise Intro--Sample--Read consistency, and
hiding/fibre checks hold exactly. The remaining IntroA--IntroB edge may be
made automatically accepting, so the whole resulting measurement
presentation has value one.

Nevertheless, even allowing the central Pauli sign, there is no nonzero
multiplicity projection on which the two gauges agree:

```text
||R(sigma_z - sigma_x)||_2^2 = 2 tau(R),
||R(sigma_z + sigma_x)||_2^2 = 2 tau(R).                  (BQA2)
```

Thus neither orientation has a positive exact corner, and an
`o(1)` comparison can hold only on an `o(1)` corner. Pauli-X
translations merely dress the label operator in `(BQA1)` and retain
`sigma_z`; they never turn that occurrence into `I tensor sigma_z`.
An autoaccept detyping anchor has answer length zero and hence carries no
unreadable observable at all.

Consequently BCV Question Reduction provides strategy-level block normal
forms, not a same-reservoir group-relator gadget. A positive bridge must add
a non-autoaccept mixed relation which compares the two answer occurrences
(or an equivalent finite-matrix cross-Gram incidence). If that comparison
is conditioned on the sampled readable seed, it is precisely the
selector-controlled relation that the ZPC-to-LCS compiler still has to
linearize; it cannot be counted as a free anchor.
