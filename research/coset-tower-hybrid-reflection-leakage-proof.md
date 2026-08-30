---
rg: 2
id: coset-tower-hybrid-reflection-leakage-proof
kind: route
title: Expand the hybrid square into its orthogonal payload-leakage corners
target: coset-tower-hybrid-reflection-pays-exact-payload-leakage
requires: []
---

Let `(E_i)` be a PVM in a finite tracial von Neumann algebra, let each
`A_i` be a self-adjoint unitary, and put `R=sum_i E_i A_i E_i`.  Orthogonality
of the `E_i` kills every cross term in `R^2`.  On the `i`-th diagonal block,

```text
E_i-E_iA_iE_iA_iE_i = E_iA_i(1-E_i)A_iE_i >= 0.
```

Taking traces and summing gives

```text
tau(1-R^2)=sum_i ||(1-E_i)A_iE_i||_2^2.
```

The two off-diagonal corners of `[E_i,A_i]` are adjoints and are
Hilbert--Schmidt orthogonal, so the right side is also
`(1/2)sum_i ||[E_i,A_i]||_2^2`.  Since every summand is nonnegative,
`R^2=1` holds exactly when every `E_i` reduces its payload `A_i`.  This is
the asserted exact authentication/leakage identity.

For the native shell, if the same atom `E_i` reduces every generating lamp
reflection, then it commutes with the von Neumann algebra they generate;
hence `E_i` lies in `M' cap M=Z(M)=C`.  A nontrivial multi-atom tower
therefore cannot be a common reducing selector for the full native payload.
