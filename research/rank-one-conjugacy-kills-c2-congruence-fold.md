---
rg: 2
id: rank-one-conjugacy-kills-c2-congruence-fold
kind: claim
title: One rank-one conjugacy kills every C2-sheet congruence fold
artifacts:
  - research/c2-congruence-fold-sign-proof.md
distinct_from:
  closed-a2-loop-still-leaves-swap-fold-free: that exact counterpacket twists both negative-root and Weyl slots by the sheet sign but omits the rank-one conjugacy used here; this proves that the omitted relation closes the entire C2-character family containing that packet.
  two-mixed-a2-words-do-not-control-fold-square: that dihedral packet collapses the positive roots and does not carry an exact congruence actor; this theorem concerns tensor products of an exact odd-congruence actor with arbitrary C2 slot signs.
  sl3-swap-extension-has-defect-only-fold-square-rigidity: that asks for a dimension-free approximate theorem for every assignment of the full presentation; this is an exact theorem only for the C2-sheet congruence sector.
---

Let `rho` be any exact finite-dimensional representation of the odd-level
congruence actor used in `closed-a2-loop-still-leaves-swap-fold-free`.  Tensor
it with a two-dimensional sheet carrying

```text
S=Z tensor 1,                  H=G tensor rho(h),       (RCK1)
```

where `G` is an arbitrary sheet unitary.  Allow each of the four simple-root
slots `E_12,E_23,B_21,B_32` to acquire an arbitrary factor in `{1,Z}`, and
define the doubled-root and Weyl slots by the two displayed rank-one package
relations.

If the two closed `A_2` returns

```text
W_12E_23W_12^*=[E_12,E_23]=W_23^*E_12W_23             (RCK2)
```

hold, and one also imposes the genuine rank-one Weyl conjugacy

```text
W_12E_12W_12^*=B_21,                                  (RCK3)
```

then the unbalanced torus equation `R_tor=1` forces `G=1`.  Consequently

```text
HSH^*S=1.                                              (RCK4)
```

There is also an explicit robust form with only the torus word allowed to
have defect.  Keep the congruence actor, the discrete sign placements, the
closed loop, and `(RCK3)` exact, and set

```text
eta=||R_tor-1||_2.
```

Then

```text
||G-1||_2=eta,
||HSH^*S-1||_2<=2 eta,
||(HSH^*S)^2-1||_2<=4 eta,                             (RCK5)

tr(QPQ-(QPQ)^2)<=eta^2/2.                             (RCK6)
```

Thus the collapse is dimension-free and quantitatively stable against the
remaining torus-relator error inside this exact discrete-sign sector.

Thus `(RCK3)` detects not only the particular packet already recorded in
`closed-a2-loop-still-leaves-swap-fold-free`, but every placement of a central
two-sheet sign on the same exact congruence packet.

This does not prove the full fold-square terminal.  It shows precisely that
the next enemy cannot be another scalar `C_2` character on the congruence
actor.  Any stronger exact countermodel must use a noncentral multiplicity
gauge, a non-congruence actor outlier, or omit another genuine lattice
relation.

DERIVATION
c2-congruence-fold-sign-proof
