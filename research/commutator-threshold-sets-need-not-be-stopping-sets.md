---
rg: 2
id: commutator-threshold-sets-need-not-be-stopping-sets
kind: claim
title: Threshold sets of exact parity commutator magnitudes need not be stopping sets
distinct_from:
  unique-neighbor-ldpc-checks-force-dense-noncommutation: that applies at threshold zero; this gives an exact one-check counterexample at a positive threshold.
  sparse-clifford-cycles-refute-average-commutator-rounding: that uses a growing sparse sign graph; this obstruction already occurs inside one exact parity face by mixing its character atoms.
---

The stopping-set proof cannot be integrated over commutator thresholds.  In
a direct sum of two `2 x 2` blocks, choose commuting diagonal reflections
`Q_1,Q_2,Q_3` with

```text
Q_1 Q_2 Q_3=I.
```

On the first block let their signs relative to the two basis vectors differ
by `110`, and on the second by `101`.  Let `W` be the Pauli X reflection on
each block, and give the two blocks equal normalized trace.  Then

```text
(||[Q_1,W]||_2^2, ||[Q_2,W]||_2^2, ||[Q_3,W]||_2^2)
  = (4,2,2).                                                (CTS1)
```

Thus the positive support `{1,2,3}` obeys the parity stopping condition, but
the level set at any threshold strictly between `2` and `4` is the singleton
`{1}`.  More generally, convex mixtures of local character atoms let large
commutator mass split among different partner coordinates.

Hence a layer-cake argument cannot apply stopping expansion separately to
the spectral or norm level sets.  The exact magnitude information is only
the fundamental-cone inequality of
`adjoint-parity-defects-form-tanner-fundamental-cone`.  A successful
dimension-free bootstrap needs an operator-valued cosystolic/LTC estimate
that controls these mixtures and aligns them across checks.
