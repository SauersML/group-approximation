---
rg: 2
id: central-involution-corner-exactification
kind: claim
title: An approximate central involution yields an exact reducing microstate corner
artifacts:
  - research/central-involution-corner-exactification-proof.md
distinct_from:
  central-packet-sign-supplies-marked-carrier: that rounds the sign and obtains an approximately reducing carrier with an explicit energy bound; this additionally block-diagonalizes and polar-corrects the other generators so the corner carries unitary microstates.
  kazhdan-almost-invariant-corner-near-invariant-projection: that corrects a subspace for an already exact representation; this corrects the finite microstate tuple relative to a central involution.
---

Let `J` be a central involution in a finitely generated group, and let
`phi_n` be inverse-normalized normalized-Hilbert--Schmidt microstates on
windows containing `J`, a fixed finite inverse-closed generator set, and
their centrality products.  After perturbing every fixed generator by
`o(1)` in normalized Hilbert--Schmidt norm, one may arrange

```text
psi_n(J)=Z_n=Z_n*=Z_n^-1,
[Z_n,psi_n(s)]=0
```

exactly.  The perturbation preserves all fixed multiplication defects and
word traces up to `o(1)`, as well as inverse normalization.

If `e_n=(1-Z_n)/2` has rank ratio bounded away from zero, then restriction
to `e_n` is a unitary microstate with normalized corner defects still
`o(1)`.  If the original microstates have canonical trace and `J!=1`, then
`rank(e_n)/d_n ->1/2`; for every `g` commuting with `J`, its corner trace is

```text
tau_e(e_n psi_n(g)e_n)
 = [tau(psi_n(g))-tau(Z_n psi_n(g))]/[2 tau(e_n)].
```

