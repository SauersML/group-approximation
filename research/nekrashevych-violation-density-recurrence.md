---
rg: 2
id: nekrashevych-violation-density-recurrence
kind: claim
title: The twisted tree return converts Schur violation density into a strict Fanizza contraction
distinct_from:
  subtree-trace-independence-certificate: that controls covariance of two sibling observables; this must also orient every fixed BCS predicate packet, pay inactive sectors, and identify the returned child carrier with the next Fanizza level.
  schur-violation-density-gives-contraction: that proves the scalar inequality once the active, violating, and returned masses satisfy its three hypotheses; this constructs those masses from the tree packet words.
---

Inside `nekrashevych-clifford-sign-tape`, place the fixed Schur packets for the
Fanizza BCS menu so that their character-density observables and partial-center
returns define masses `a_n,v_n,c_n` satisfying `(SVG1)--(SVG3)` with

```text
delta_n+eta_n <= C(n+1)^k sqrt(E).                         (NVR1)
```

The same fixed group relators must reset the old selector character, align the
returned child multiplicity with the next context, and preserve the separate
marked completeness channel.  The resulting coefficient may be any fixed
`lambda=(1+beta)^(-1)<1`; the contraction ladder does not require the special
value `1/2`.

## Attempts

- Spin-factor independence is not a substitute for renewal:
  `schur-violation-density-is-in-the-spin-commutant` proves that the predicate
  density is fixed by the spin expander.  The active route instead uses the
  balanced full reset to obtain a fixed violation fraction and
  `partial-center-thompson-schur-return` to renew the selector chart.
- The unresolved calculation is the endpoint intersection in that
  partial-center return.  Tree conjugacy preserves trace but does not by
  itself renew selector character, so a placement which merely puts the next
  packet in the external commutant is rejected.
