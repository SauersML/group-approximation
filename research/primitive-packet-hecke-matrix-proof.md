---
rg: 2
id: primitive-packet-hecke-matrix-proof
kind: route
title: Saturate the group corner by primitive packet matrix units
target: primitive-packet-corner-is-matrix-over-hecke-atom
requires: []
---

Matrix-unit multiplication gives

```text
E_(1k) Psi((a_ij)) E_(l1)=a_kl,
sum_(i,j) E_(i1) E_(1i) x E_(j1) E_(1j)=pxp=x.
```

Thus `Phi` and `Psi` are inverse star homomorphisms.  Applying `Phi` to a
root matrix unit gives the corresponding scalar matrix unit over `e`, which
proves the root-block and subcorner identifications.

If `U` normalizes the scalar diagonal, its adjoint action permutes the
diagonal minimal projections.  Multiplying `U E_ii=E_(sigma(i),sigma(i))U`
by packet matrix units leaves exactly the one block `(PMH8)`; the two unitary
identities make that block a unitary of `H`.  This proves `(PMH7)` and its
converse.

Finally, for diagonal signs the `(i,j)` entry of `[U,d_k]` is

```text
(d_k(j)-d_k(i)) Phi(U)_ij.
```

Over `C` it vanishes for every `k` exactly when the two indices have the same
joint sign pattern.  This gives the direct sum `(PMH10)`.  Singleton fibers
leave only diagonal Hecke units, which fix every context atom; nonsingleton
fibers are the only possible escaped blocks.

An automorphism of the finite-dimensional marginal algebra permutes its
minimal projections `f_omega`.  Unitary conjugation preserves their
canonical traces, and those traces are `|I_omega| tau(e)`, so only equal-size
fibers can be permuted.  The same matrix-block multiplication as above then
gives one square unitary over `H` in every permuted block and zeros elsewhere;
the converse is immediate.  These computations prove the claim.
