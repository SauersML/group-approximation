---
rg: 2
id: center-chain-common-source-authenticates-native-covariances
kind: claim
title: Authenticate the common-source mixed Hecke maps as the two native selector covariances
distinct_from:
  center-chain-mixed-hecke-overlap-is-common-pauli-source: that establishes the exact Hecke common source, common range, relative polar, and Pauli-commutant factorization; this asks for the remaining comparison with the separately prescribed native selector rows.
  center-chain-hecke-flags-authenticate-native-occurrences: that refuted claim asks for a fixed exact ordinary-word identification on a nonzero regular corner; this permits only matrix-model-dependent cuts whose discarded mass is controlled by the canonical microstate defects.
  center-chain-mixed-hecke-polars-share-a1-tail: that identifies the two polar-word squares with the literal coefficient roots; a square-root identity alone does not identify the selector source and controlled-target projections.
---

**OPEN FINITE-MATRIX NATIVE-COVARIANCE LEAF.**  Let

```text
S_i=V_iQ:QH -> PH
```

be the exact common-source/common-range restrictions from
`center-chain-mixed-hecke-overlap-is-common-pauli-source`.  In every
canonical-trace finite matrix model with packet defect `delta`, construct
model-dependent subprojections of `Q` and `P`, losing only
`O(delta^alpha)` ambient normalized trace for some fixed `alpha>0`, on which
the two prescribed native selector-row transports are within
`O(delta^alpha)` normalized Hilbert--Schmidt distance of `S_1,S_2` after
the allowed fixed packet label relabelings.

The comparison must authenticate the actual source reflections and
controlled target reflections of the two rows with ratios

```text
(1/2,1/4),                 (1/4,1/8),
```

not merely reuse the four equal numerical Hecke support traces.  It must
also preserve the factorization

```text
S_1^*S_2=B_2R,
[R,A_1Q]=[R,B_1Q]=0,
```

so that the `B_2` action is charged to the literal first selector root and
`R` is the common reservoir gauge.

All internal Hecke geometry is already exact.  The only remaining issue is
why canonical finite matrix coordinates, unlike the canonical regular
representation, must choose these Hecke maps for the two native
occurrences.  A fixed group-algebra comparison is forbidden by
`fixed-center-chain-hecke-occurrence-is-regularly-impossible`; the proof
must use a genuinely coordinate-dependent spectral or polar choice whose
loss vanishes with the ordinary relation defect.

## Square-root fence

The identities

```text
u_1^2=x_87(s_(00)t_0),
u_2^2=x_98(s_(000)t_(00))
```

do not by themselves prove this claim.  Even in finite matrices, specifying
the square of a unitary leaves arbitrary choices on the two spectral
subspaces of the involution.  The native selector covariance contains the
additional source/controlled-target typing which selects the relevant
choice.  A valid proof must use those native row relations, not only the
two polar-square identities.

## Attempts

- **Use the polar squares as occurrence certificates.**  This stops at the
  square-root fence above: the identities determine the coefficient roots
  but not the source and controlled-target projections of either native
  row.
- **Use the exact common source as a fixed native carrier.**  This is
  forbidden by `fixed-center-chain-hecke-occurrence-is-regularly-impossible`.
  On a fixed positive regular corner the two native affine equations force
  the incompatible gauge fractions `1/2` and `5/6`.  Any surviving proof
  must therefore extract its comparison only in finite matrix coordinates
  and charge every discarded direction to the microstate defect.
