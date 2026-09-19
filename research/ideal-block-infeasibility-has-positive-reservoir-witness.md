---
rg: 2
id: ideal-block-infeasibility-has-positive-reservoir-witness
kind: claim
title: Native ideal-block Choi infeasibility has a positive reservoir-annihilating witness
distinct_from:
  finite-packet-triangle-repair-is-ideal-block-choi-feasibility: that gives an arbitrary signed separator annihilating the whole reservoir image; this replaces it, on the actually relevant unit-zero correction space, by a positive Choi functional on the same native finite-dimensional ideal block.
  tree-face-separator-signedness-is-removable-modulo-the-unit: that positivizes one quotient-level finite-face component whose GNS representation need not be finite-dimensional; this works packetwise inside the prescribed representation of the relator ideal, sums all three positive face components, and has a bound uniform in the packet dimension.
  native-relator-soft-modes-persist-in-simple-ideal-blocks: that shows maximal ideal support and low relator energy alone do not give a spectral angle; this couples failure of the affine Choi repair itself to positivity, without deriving a spectral gap from support.
---

**ESTABLISHED (dimension-uniform positive conversion).**  In the explicit
three-face triangle let

```text
E=S_Delta=C^*(P_12)+C^*(P_23)+C^*(P_13),
B_ij=C^*(P_ij).
```

Let `J` be any finite-dimensional unital C-star algebra with unit `z`, and let
`T:E->J` be a unital self-adjoint linear map, so `T(1)=z`.  Let `V` be a real
linear space of self-adjoint maps `E->J`, and put

```text
V_0={v in V:v(1)=0}.                                      (PIW1)
```

If

```text
(T+V) intersect UCP_z(E,J)=empty,                         (PIW2)
```

then there is a nonzero real linear functional `Omega` on the self-adjoint
map space such that

```text
Omega(psi)>=0                 for every cp psi:E->J,
Omega(v)=0                    for every v in V_0,
Omega(T)>sup{Omega(theta):theta in UCP_z(E,J)}.            (PIW3)
```

Thus `Omega` is a positive Choi functional on the **same** finite-dimensional
target block, not a positive GNS functional obtained only after passing to a
quotient-level limit.  It detects the actual affine repair discrepancy and
annihilates every reservoir correction which could occur in a unital repair.

Moreover there is a constant `C_Delta<infinity`, depending only on the three
fixed finite face algebras and a fixed linear face splitting of `E`, with the
following quantitative property.  If the signed strict separator is
normalized to `||F||=1`, `Omega` can be chosen so that

```text
||Omega||<=C_Delta                                           (PIW4)
```

while its strict separation gap is **exactly** the gap of `F`.  Thus after
normalizing the positive witness, the guaranteed gap loses at most the fixed
factor `C_Delta`, independently of `J`, the packet dimension, the ideal
support projection, and the reservoir depth.

Apply this to `(IBC4)` with

```text
T=z rho o t,
V=rho_* L_sa(E,L) subset L_sa(E,J),
J=rho(I).
```

Since every point of `UCP_z(E,J)` sends `1` to `z`, `(IBC4)` is feasible
exactly when `(T+V_0)` meets that cone slice.  Consequently failure of a
prescribed finite relator reservoir in a prescribed finite representation
packet always has a dimension-uniformly conditioned positive native-ideal
Choi witness satisfying `(PIW3)`--`(PIW4)`.

**Sharp scope.**  This closes the signedness and packet-dimension conditioning
holes for the actual affine Choi discrepancy.  It does not yet identify a
single vector in the packet on which both the positive Choi gap and small
native-relator energy hold, nor does it show that the resulting positive
certificates are compatible as the reservoir depth changes.  That correlation
or compactness step, rather than positivity of the packet separator, is the
remaining obstruction.

Proof: `split-native-separator-over-finite-faces-and-positivize`.

DERIVATION
split-native-separator-over-finite-faces-and-positivize
