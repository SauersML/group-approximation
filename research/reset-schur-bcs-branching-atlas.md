---
rg: 2
id: reset-schur-bcs-branching-atlas
kind: claim
title: A reset HNN atlas returns the full Schur BCS child carrier with polynomial HS loss
distinct_from:
  toeplitz-schur-child-masa-recurrence: that follows the satisfying-oriented Fanizza tape and must pay its inactive FDB1 sectors; this uses a fixed non-CE BCS at every level, orients each rank gate toward violation, and returns the full one-plus-violation child carrier.
  branch-reset-amalgam-preserves-mark-and-balances-types: that resets one old selector chart and preserves a mark; this must assemble those cells recurrently and retain the robust BCS violation mass at every returned level.
---

For one fixed finite BCS with a tracial state but no Connes-embeddable tracial
state, construct a finite recurrent presentation from its context-local
Schur--Clifford violation packets, branch-controlled selector resets, and HNN
chart transports, with the following uniform property.

For every finite-dimensional normalized-HS tuple of relator energy `E`, its
level-`n` returned carrier has normalized baseline-packet mass `a_n`; after
local exactification it has forbidden mass `v_n` and full `Q`-child mass
`c_n`. There are fixed `beta,C,k>0` such that

```text
v_n >= beta a_n-C(n+1)^k sqrt(E),                     (RSA1)
c_n = a_n+v_n,                                        (RSA2)
a_(n+1) >= c_n-C(n+1)^k sqrt(E).                      (RSA3)
```

Every relator is used with uniformly bounded overlap in these estimates. The
presentation also has an exact representation in which the marked word is
nonidentity and the level-zero carrier has positive mass.

The original shared BCS words must be tested before contextwise packet
correction, so `(RSA1)` is the robust noncommutative BCS gap rather than a
classical assignment gap. Different context selector charts must not be made
globally commuting. The reset cell removes the old selector center, and the
HNN edge aligns its complete branch-type vector with the next context chart;
neither operation may discard the `q` branch label which distinguishes the
two violating child simples.

This target is deliberately finite and quantitative. It asks only for the
remaining compatibility of the already explicit reset and HNN cells around
one recurrent atlas, not for a new nonlinear scalar group word and not for
Fanizza inactive-sector payment.

## Attempts

- **Literal nesting:** invalidated by
  `nested-schur-multiplicity-wire-globalizes-selectors`.
- **Plain HNN return:** invalidated by
  `hnn-conjugacy-cannot-return-schur-morita-multiplicity`; the HNN edge is used
  only after child branching, to preserve and align the resulting types.
- **Reset then align:** active. `branch-controlled-pauli-selector-reset`
  removes the old center, `branch-reset-amalgam-preserves-mark-and-balances-types`
  controls reset loss, and `hnn-selector-chart-transport-preserves-mark-and-types`
  controls chart-alignment loss. The unresolved point is to make these local
  corrections share one recurrent carrier while retaining the original
  shared-word forbidden mass in `(RSA1)` with bounded overlap.
