---
rg: 2
id: groupify-schur-child-center-chart
kind: claim
title: Groupify the selector-controlled center of a Schur child packet
distinct_from:
  schur-complement-controls-relative-pauli-module: that constructs the corrected child-center involution inside the finite group algebra; this must expose its two spectral charts by finitely many group relations with dimension-free HS control.
  finite-predicate-signed-permutation-sector: that realizes arbitrary predicate support inside one finite representation block; this additionally must remain compatible with the shared Schur baseline and its child restriction multiplicities.
  raw-schur-generator-is-not-child-center: that rules out the raw last generator; this asks for a valid replacement.
---

For each fixed Schur predicate packet, construct a finite group-theoretic or
signed-Hecke chart exposing the two central projections

```text
(I+Q_f)/2, (I-Q_f)/2,
```

where `Q_f` is the explicit selector-controlled group-algebra involution in
`(RSC2)`, with the following properties.

1. In every exact marked packet representation, the chart types are exactly
   the two simple types of the `Q` child, including both violating children.
2. In every approximate matrix representation, local exactification and chart
   alignment lose at most `C sqrt(E)` normalized weighted multiplicity.
3. The chart admits a finite transverse reset and HNN transport to a fresh BCS
   context without imposing commutation between different contexts.
4. Amalgamating the chart and transport with a marked base preserves an exact
   representation in which the marked word remains nonidentity.

The final object must be an ordinary finitely presented group. Replacing
`Q_f` by raw `q_(N+1)` is forbidden by
`raw-schur-generator-is-not-child-center`; replacing it by a scalar predicate
word is forbidden by `schur-rank-output-is-not-a-scalar-selector`.

## Attempts

- **Use raw `q_(N+1)`: fails.** It anticommutes with the baseline generator
  `p_t`, so its eigenspaces are not child modules.
- **Use one selector word:** fails for nonlinear `v(x)` by the affine-selector
  barrier.
- **Signed-Hecke chart:** active. The orthogonal selector idempotents make
  `Q_f` an explicit finite group-algebra involution, so a finite regular block
  can expose its spectral projections. The missing step is an ordinary-group
  projection atlas whose approximate representations retain those blocks with
  dimension-free HS loss and whose exact amalgam preserves the marked model.
