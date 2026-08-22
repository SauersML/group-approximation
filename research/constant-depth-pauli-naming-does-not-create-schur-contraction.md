---
rg: 2
id: constant-depth-pauli-naming-does-not-create-schur-contraction
kind: claim
title: Naming every constant-depth Pauli cell solves localization but does not create the Schur contraction
artifacts:
  - research/artifacts/diagonal-covariant-pauli-incidence-and-constant-depth-audit-2026-08-21.md
distinct_from:
  finite-packet-cannot-realize-absorbing-contraction: that refutes a complete contraction theorem internal to one finite packet by its negative regular representation; this pinpoints what remains after all finitely many coordinate commutators and Morita charts are explicitly named.
  schur-child-toeplitz-morita-wire: that reconstructs the doubled multiplicity algebra from two transverse child commutants; this shows that such reconstruction is not an oriented loss of one child.
---

Fix the terminal depth `m` before presenting the group.  One may name every
old-spin coordinate Pauli `P_(n,i),Q_(n,i)` and every Fanizza chord `U_n`
for `n<=m`, and impose the finitely many relations

```text
[U_n,P_(n,i)]=[U_n,Q_(n,i)]=1                          (CDP1)
```

together with all required selector--Pauli cross-commutators.  Fixed finite
packet exactification may then have constants depending on `m`.  In the
properly infinite completeness representation, put each new finite spin
packet in the preceding spin commutant and absorb all finite Morita
multiplicities in an infinite residual factor.  Thus finite-depth naming
does solve the coordinate localization and exact-model compatibility
problems without any shift synchronization.

It does **not** prove `constant-depth-schur-lift-of-doubling-tape`.
Relations `(CDP1)` place each new cell and its Gram deficiency in an old-spin
commutant, but say nothing that orients the two Schur children or yields

```text
a_n <= lambda a_(n+1)+error,          lambda<1.          (CDP2)
```

The two transverse child commutants in
`schur-child-toeplitz-morita-wire` generate the doubled `A_f` multiplicity
algebra exactly; this Morita reconstruction is rank/current conserving.
Without a further proper-corner, holonomy, or contextual operator relation,
neither child is selected or charged.  If the entire proposed inference
were instead a theorem about the resulting fixed finite packet, its negative
regular summand would supply a stationary zero-defect model and contradict
an absorbing chain, exactly as in
`finite-packet-cannot-realize-absorbing-contraction`.

Proper infiniteness proves completeness only: it absorbs the finite packet
sizes but gives no finite-matrix soundness inequality and no positive-density
current.  The exact remaining constant-depth terminal is therefore an
**amplification-stable, positive-density one-sided child payment** in the
joint infinite ambient group.  It is not Pauli localization, clock
synchronization, or finite Morita reconstruction.
