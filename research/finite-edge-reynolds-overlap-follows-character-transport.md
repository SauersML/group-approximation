---
rg: 2
id: finite-edge-reynolds-overlap-follows-character-transport
kind: claim
title: A finite-edge Reynolds checksum follows the induced central-character permutation
distinct_from:
  finite-character-idempotents-have-exact-hnn-transport: that transports individual central character idempotents and assembles algebraic corner unitaries; this computes the corresponding conditioned adjoint Reynolds ranges and their scalar-overlap support.
  paired-frame-hard-characters-form-forced-two-cycle: that exhaustively identifies the hard permutation for one order-128 frame; this is the general representation-theoretic law showing why the scalar checksum inherits it.
  adjoint-reynolds-return-needs-one-overlap-moment: that proves one large overlap is enough for a rank contradiction; this identifies which character carrier an ordinary finite HNN edge can overlap.
---

Let `phi:H_+->H_-` be an isomorphism of finite groups carrying a central
abelian subgroup `Z_+` isomorphically to `Z_-`.  Let `K` contain `H_+,H_-`
and a stable letter `t` with

```text
t h t^-1=phi(h),                  h in H_+.             (FEO1)
```

In an exact finite-dimensional unitary representation `rho` of `K`, let
`e_(+,chi)` and `e_(-,psi)` be the central-character projections for
`chi in dual(Z_+)` and `psi in dual(Z_-)`.  Put

```text
sigma(chi)=chi compose phi^(-1)|_(Z_-).                 (FEO2)
```

Then

```text
rho(t)e_(+,chi)rho(t)^*=e_(-,sigma(chi)).               (FEO3)
```

Let `R_(+,chi)` be the orthogonal projection on `End(H_rho)` onto operators
supported on `e_(+,chi)H_rho` and commuting there with `rho(H_+)`; define
`R_(-,psi)` analogously.  For `T=Ad_(rho(t))`,

```text
T R_(+,chi) T^*=R_(-,sigma(chi)).                       (FEO4)
```

Consequently the conditioned overlap

```text
tr_ad(R_(+,chi) T^* R_(-,psi) T R_(+,chi))              (FEO5)
```

vanishes whenever `psi!=sigma(chi)`.  A finite-edge scalar checksum cannot
silently keep the old ownership label: it authenticates precisely the
transported character sector.

For the paired support frame,
`paired-frame-hard-characters-form-forced-two-cycle` gives

```text
sigma:101 <-> 011.                                      (FEO6)
```

Thus its exact edge transports the forbidden carrier into the unique reverse
reservoir, and a scalar-overlap reformulation does not remove the need to
orient or exhaust that reservoir by an infinite label.
