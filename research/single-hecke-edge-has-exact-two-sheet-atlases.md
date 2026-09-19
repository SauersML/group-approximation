---
rg: 2
id: single-hecke-edge-has-exact-two-sheet-atlases
kind: claim
title: Every single arithmetic Hecke edge has exact finite two-sheet atlas models
invalidates:
  - sl3-coset-nonsoficity-via-one-hecke-edge
distinct_from:
  sl3-prime-coset-action-exact-atlas-firewall: that excludes a two-site atlas inside an exact finite action of the full S-arithmetic actor; this constructs exact finite atlases for the one-edge HNN group and proves that the omitted full-actor relations carry all of the obstruction.
  sofic-coset-atlas-linearizes-to-exact-quasiregular-coboundary: that extracts a Hilbert-space packet from a hypothetical full atlas; this gives literal finite permutation models for every one-edge packet.
---

Fix a prime `p`, put

```text
Lambda=SL_3(Z),       Gamma=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)),   I=Lambda cap h^(-1)Lambda h,
phi(c)=h c h^(-1)  (c in I),
E_h=<Lambda,t | t c t^(-1)=phi(c), c in I>.             (HEA1)
```

For every integer `m>=2` coprime to `p`, the one-edge group `E_h` has an
exact finite action on

```text
Omega_m=SL_3(Z/mZ) x Z/2                                (HEA2)
```

with a two-site label `ell(x,j)=j` such that

```text
ell(c omega)=ell(omega)       (c in Lambda),
ell(t omega)=1-ell(omega)     (omega in Omega_m).         (HEA3)
```

Thus the base-site label is exactly `Lambda`-invariant and the adjacent
Hecke letter moves it at every point.  This is a perfect finite atlas for
the window consisting of one vertex and one oriented Hecke edge, even with
all relations of `Lambda` and all conjugacy relations over `I` imposed
exactly.

Consequently the noncorrectability theorem
`sl3-prime-coset-action-exact-atlas-firewall` genuinely uses exactness of
the **full** `Gamma` action.  It cannot be localized to one parahoric edge.
Kazhdan averaging on `Lambda`, exactification of the `Lambda` action, and
one overlap transporter are jointly compatible with `(HEA3)`.  Any proof
that the action `Gamma curvearrowright Gamma/Lambda` is nonsofic must charge
at least one additional full-actor relation, equivalently a rank-two
chamber/holonomy compatibility not present in `(HEA1)`.

This does not construct a sofic atlas for the full arithmetic action.  The
sheet flip cannot extend to an exact finite `Gamma` action: modulo `m`, the
image of `h` already lies in the image of `Lambda`, while the flip does not.

DERIVATION
single-hecke-edge-two-sheet-atlas-proof
