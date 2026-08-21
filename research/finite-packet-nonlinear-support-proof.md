---
rg: 2
id: finite-packet-nonlinear-support-proof
kind: route
title: Induce every marked selector character to the finite packet
target: finite-packet-central-sign-cannot-enforce-nonlinear-support
requires: []
---

Fix `chi in dual(A)` with `chi(J)=-1` and decompose
`Ind_A^K chi` into irreducibles.  Frobenius reciprocity gives an irreducible
constituent `pi` with

```text
Hom_A(chi,Res_A^K pi) != 0.
```

Since `J` is central, Schur's lemma makes `pi(J)` scalar.  Its action on the
nonzero `chi`-weight space is `chi(J)=-1`, so `pi(J)=-I`; that same weight
space realizes all selector values of `chi`.  Varying `chi` proves that the
marked sector has full selector spectrum.

For gauge doubling, write each logical selector as `d_i=A_iB_i` and let a
gauge involution multiply both shares by `J`.  Given a forbidden logical
assignment, choose share signs with that product and `chi(J)=-1`.  Every
gauge flip changes both signs together, hence preserves every product
`A_iB_i`.  Inducing the resulting character to the enlarged finite packet
therefore produces an exact marked representation whose entire gauge orbit
still has the forbidden logical assignment.  The same induction applies
after any further finite packet enlargement.
