---
rg: 2
id: atlas-hard-packet-couples-a4-line-and-s3-scalar-fingerprint
kind: claim
title: The hard packet couples one A4 line carrier and the two S3 scalar carriers on a common transport cut
distinct_from:
  a4-s3-hybrid-fingerprint-diagonalizes-s4-extension-triple: that proves the finite fingerprint is diagonal once its three rows are available; this is the word theorem that must make those rows refer to the same relative operator.
  atlas-hard-packet-authenticates-s4-extension-triple: that is the resulting extension-channel authentication statement; this isolates the new mixed A4/S3 implementation gate.
  atlas-hard-packet-s3-channel-decoder: that also needs the subsequent literal coefficient minor on the three Leavitt pairing monomials.
---

OPEN.  In the exactified regular `A4` context meeting the hard
`S4 <- S3 -> S4` cell, use the fixed central line idempotent `E_omega` (or
`E_(omega^2)`) and the exact raw-`S3` central idempotents `P_1,P_epsilon`.
For the named hard-prefix and comb transports, prove from literal packet
relators or their bounded normal-closure consequences that the three
compressions

```text
E_omega^out T E_omega^in,
P_1^out T P_1^in,
P_epsilon^out T P_epsilon^in.                         (HPC1)
```

are defined on one common finite multiplicity cut and obey the same
transport composition law, with normalized-HS loss bounded by a fixed
constant times packet defect.

The coupled rows must eliminate or determine every reduced operator source
outside the extension labels `2,3,3 epsilon`.  Once this is done,
`a4-s3-hybrid-fingerprint-diagonalizes-s4-extension-triple` identifies the
three surviving coordinates with no matrix inversion loss.

## Attempts

- `E_omega` is word-visible: it is the twelve-term central character average
  from `a4-line-carriers-explicit-idempotents`.  The `S3` scalar projections
  are the corresponding six-term character averages.  Their perturbation
  costs are therefore fixed and independent of amplification.
- The three compressions must act on the same relative transport.  Merely
  finding the three subgroup types in unrelated packet occurrences does not
  authenticate an extension label.
- No exact `S4` action may be assumed for the cross-chart hard prefix.  The
  classical `S4` restrictions supply the fingerprint only; the common-cut
  coupling has to come from named class-11/class-30, interior, or comb
  relations.
- Boundary rows alone are insufficient, and one mixed `C3` Gram remains
  locally blind.  The first audit should therefore project the full twelve
  common-product equations onto `(HPC1)` and retain every input block feeding
  those rows.
- A failure of common-cut coupling, or a surviving free reduced source in
  any of the three rows, refutes this route without affecting the abstract
  diagonal fingerprint.
