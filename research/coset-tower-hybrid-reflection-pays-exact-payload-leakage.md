---
rg: 2
id: coset-tower-hybrid-reflection-pays-exact-payload-leakage
kind: claim
title: A coset tower authenticates a hybrid reflection exactly when it reduces the payload
distinct_from:
  finite-shell-coset-tower-is-a-nonlinear-unstabilized-lift: that isolates existence of the equivariant Q/H projection algebra; this proves that such an algebra alone does not authenticate the nonlinear payload correlation needed by the Fano compiler.
  ghost-completed-fano-naimark-wordizes-one-local-predicate: that constructs one local controlled reflection in a chosen representation; this computes the exact leakage incurred when a global coset selector is used to assemble many such chosen reflections.
  fano-cap-sequential-products-form-an-algebraic-naimark-carrier: that computes mixing of a specific seven-cap Naimark projection with its selector algebra; this is the universal compression identity for any sharp tower and any assigned payload reflections.
---

**ESTABLISHED EXACT LEAKAGE IDENTITY.**  Let `(E_i)_(i=1)^n` be any PVM
in a finite tracial von Neumann algebra and let `A_i=A_i^*=A_i^(-1)` be
arbitrary payload reflections.  The most direct hybrid compression is

```text
R=sum_i E_i A_i E_i.                                  (CTH1)
```

It is a self-adjoint contraction, and exactly

```text
tau(1-R^2)
 =sum_i ||(1-E_i)A_iE_i||_2^2
 =1/2 sum_i ||[E_i,A_i]||_2^2.                        (CTH2)
```

Indeed cross terms in `R^2` vanish, while on the `i`-th tower block

```text
E_i-E_iA_iE_iA_iE_i
   =E_iA_i(1-E_i)A_iE_i>=0.                           (CTH3)
```

Taking traces gives the first equality.  The two off-diagonal corners of
`[E_i,A_i]` are adjoints and Hilbert--Schmidt orthogonal, giving the second.

Consequently `R` is a reflection if and only if every assigned tower atom
reduces its payload:

```text
R^2=1   iff   [E_i,A_i]=0 for every i.                (CTH4)
```

This is the exact extra datum omitted by a bare finite-shell fundamental
projection.  Actor covariance, pairwise tower orthogonality and
`sum_iE_i=1` contain no relation involving the `A_i`, so they do not control
the right side of `(CTH2)`.

## Consequence for the native shell

Let `M=L(W_S)` be the finite-shell graph-product factor.  If one asks the
same tower to reduce every native shell lamp reflection, then every `E_i`
lies in

```text
{c_x:x in S}' cap M=Z(M)=C.                           (CTH5)
```

Thus no nontrivial 42-atom tower can be a common reducing selector for the
full native shell algebra.  Any exact unstabilized tower, if it exists, must
mix at least some native payload direction.  Formula `(CTH2)` is the exact
energy that a proposed hybrid word must pay or separately cancel.

The regularly stabilized tower from
`finite-shell-coset-tower-is-a-nonlinear-unstabilized-lift` avoids this
obstruction because its atoms live in the external matrix tensor factor and
therefore commute with the native payload.  This explains both its positive
operator-algebraic completeness and its finite-syntax failure: descending
the rank-one matrix atom while retaining this commuting-square relation is
strictly stronger than descending the PVM alone.

## Consequence for the Fano compiler

A Q/H PVM cannot by itself authenticate the Fano hybrid reflection.  For
each profile/context row, substitute its honest local reflection for `A_i`
in `(CTH1)`.  Exact wordization requires either

1. a **payload-reducing coset tower**, proving the relevant commutators in
   `(CTH2)` vanish on the marked carrier; or
2. ordinary relations whose energy controls the sum in `(CTH2)` and whose
   exact perfect model cancels it.

If the collection of Fano payload rows generates the full marked native
factor, option 1 is impossible by `(CTH5)`.  For a proper payload subalgebra
it remains possible, but it is a new relative-commutant/commuting-square
construction and does not follow from the arithmetic tower.  Thus even a
positive solution of the unstabilized coset-tower problem would not close
the Fano common-source seam without this additional coupling.

