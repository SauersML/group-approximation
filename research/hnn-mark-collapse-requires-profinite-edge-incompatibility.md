---
rg: 2
id: hnn-mark-collapse-requires-profinite-edge-incompatibility
kind: claim
title: HNN exact mark collapse requires profinite incompatibility of the edge map
distinct_from:
  finite-edge-hnn-closures-cannot-finish-the-nonce-atlas: that starts with finite associated subgroups and proves residual finiteness of the whole HNN extension; this gives a necessary marked-word test for arbitrary associated subgroups using one compatible finite base quotient.
  power-pair-phase-hnn-has-finite-heisenberg-mark-models: that constructs a compatible quotient for one power-pair family; this is the general criterion consumed by that construction.
  hs-schur-toeplitz-root-defect-collapse: that asks for approximate matrix collapse after exact finite-dimensional invisibility is already proved; this is only the prior exact finite-quotient screening test.
---

Let

```text
H=<G,t | t a t^(-1)=theta(a), a in A>,                  (PIC1)
```

where `theta:A->B<=G` is an isomorphism, and let `w in G` be nontrivial.  If
there is a finite quotient `q:G->Q` such that

```text
q(w)!=1,
ker(q|_A)=theta^(-1)(ker(q|_B)),                         (PIC2)
```

then `w` survives in a finite quotient of `H`.  Equivalently, if every
finite-dimensional unitary representation of `H` kills `w`, then every
finite quotient of `G` compatible with the edge isomorphism must kill `w`.

Condition `(PIC2)` says precisely that `theta` descends to an isomorphism

```text
theta_bar:q(A)->q(B).                                   (PIC3)
```

This is the first screening test for an HNN-based finite-only return.  Proper
edge inclusions, distortion, different indices in the ambient base, or
failure of a partial graph map to extend do not matter if `(PIC2)` still has
a marked solution.

Failure of `(PIC2)` for every finite quotient is only necessary, not
sufficient, for normalized-Hilbert--Schmidt collapse: hyperlinear
approximations need not come from exact finite quotients.  The criterion
therefore screens candidates before the harder robust analysis begins.
