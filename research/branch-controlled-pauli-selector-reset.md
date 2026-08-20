---
rg: 2
id: branch-controlled-pauli-selector-reset
kind: claim
title: Two branch-controlled Pauli flip families reset a selector center without a nonlinear scalar word
distinct_from:
  nested-schur-multiplicity-wire-globalizes-selectors: that rules out putting the next packet directly in the old selector commutant; this supplies a finite transverse factor which removes that center first.
  controlled-central-phase-finite-group-barrier: that rules out using a nonlinear selector predicate as a central phase; this uses only the genuine Schur child bit `q` and its complement `Jq`.
---

Let `J,q,z_1,...,z_k` be commuting central involutions in a child packet and
work on the marked sector `J=-1`. Adjoin involutions

```text
s_i^-, s_i^+       (1<=i<=k)
```

with different indices and signs commuting, fixing `J,q`, and satisfying

```text
[s_i^-,z_j]=q^(delta_ij),
[s_i^+,z_j]=(Jq)^(delta_ij).                                  (BPR1)
```

These relations define a finite class-two 2-group extension. On the child
branch `q=-1`, the pairs `(z_i,s_i^-)` are Pauli and the `s_i^+` commute with
the selector algebra. On `q=+1`, the pairs `(z_i,s_i^+)` are Pauli and the
`s_i^-` commute. Consequently, on **each** child branch the old selector
center and the appropriate reset family generate a full matrix factor
`M_(2^k)`, whose commutant forgets the old selector characters.

The reset is uniform and finite because the context arity `k` is fixed. It
does not by itself prove marked completeness: adjoining the reset forces
balanced old-selector spectra inside each relevant child branch. A global
compiler must realize those balances by a context atlas or infinite induced
model while preserving the Fanizza mark.

