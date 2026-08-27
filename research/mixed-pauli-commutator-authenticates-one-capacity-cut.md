---
rg: 2
id: mixed-pauli-commutator-authenticates-one-capacity-cut
kind: claim
title: One mixed Pauli commutator exactly authenticates one capacity cut
distinct_from:
  canonical-root-coordinate-is-binary-not-an-l2-authenticator: that rules out an independent root; this identifies it with the same-reservoir commutator.
  orthogonal-hecke-row-packs-common-source-energy-into-one-root: that treats a full multi-context row; this is the exact one-cut identity.
  global-covariance-misses-capacity-compression: that leaves the capacity commutator uncontrolled; this names it directly.
---

For self-adjoint unitaries `X,Z` and `Q=(I+X)/2`,

```text
||ZQ-QZ||_2^2=1/4||XZXZ-I||_2^2
```

in every finite tracial von Neumann algebra.  Coupling a root coordinate by
the mixed word `Y=XZXZ` therefore authenticates the capacity leakage exactly
and excludes the decoupled-factor countermodel.  It does not collapse `Y`;
that second job must come from a genuinely finite-dimensional infinite
actuator, not a finite universal packet.
