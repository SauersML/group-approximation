---
rg: 2
id: inverting-two-adds-no-stable-steinberg-projective-class
kind: claim
title: Inverting two adds no stable Steinberg projective class
distinct_from:
  solenoid-absorption-cascade-converges: that uses only the absence of 3-primary torsion in K_2(Z[1/2]) for a twisted-coboundary obstruction; this computes the entire localization map and its relative stable projective consequence.
  schur-clock-router-has-maximal-projective-leak: that permits arbitrary scalar arrow cocycles on a finite block router; this proves that no new stable arithmetic Steinberg multiplier is created when passing from Z to Z[1/2], while leaving multiplicity routers untouched.
  projective-trace-square-transfer-for-sl3-pair: that is a rank-three normalized-HS inequality for arbitrary approximate representations; this is an exact stable central-extension calculation and explicitly does not imply that inequality.
---

Let `R=Z[1/2]`.  The localization map induces an isomorphism

```text
K_2(Z)  -->  K_2(R).                                  (KST1)
```

Consequently the stable elementary-group map

```text
E(Z) --> E(R)
```

has no new relative Schur-multiplier class: restriction along this map is
injective on circle-valued projective multipliers,

```text
H^2(E(R),T) --> H^2(E(Z),T).                           (KST2)
```

In particular, a stable Steinberg projective representation of `E(R)` whose
multiplier is trivial on `E(Z)` already has globally trivial multiplier.

## Proof

Quillen localization for the closed prime `(2)` in `Spec(Z)` contains the
exact segment

```text
K_2(F_2) --> K_2(Z) --> K_2(Z[1/2]) --> K_1(F_2).      (KST3)
```

Quillen's calculation of the K-theory of finite fields gives

```text
K_2(F_2)=0,       K_1(F_2)=F_2^x=0.                   (KST4)
```

Exactness of `(KST3)` therefore proves `(KST1)`.  (In particular both groups
are the familiar `Z/2`, but their separate identification is not needed.)

For the stable elementary group, the Steinberg extension

```text
1 --> K_2(S) --> St(S) --> E(S) --> 1                 (KST5)
```

is universal central, naturally in the ring `S`.  Hence

```text
H_2(E(S),Z) = K_2(S).                                  (KST6)
```

The groups `E(S)` are perfect.  Since `T` is divisible, the universal
coefficient sequence identifies

```text
H^2(E(S),T) = Hom(H_2(E(S),Z),T).                      (KST7)
```

Under `(KST7)`, restriction of multipliers is precomposition with the map on
`H_2`.  Equation `(KST1)` makes that map an isomorphism, so restriction is
injective.  This proves `(KST2)` and the final assertion.

## Exact consequence for the SL3 projective-transfer program

This closes one tempting scalar route but not the transfer theorem.  A
projective clock cannot be justified by saying that localization at `2`
creates a central Steinberg class invisible over the integral subgroup: no
such **stable** relative class exists.  Moreover the inner-superoperator
form of projective trace-square transfer already quotients out scalar
cocycles.

The calculation does **not** identify the unstable multiplier of
`SL_3(Z[1/2])` with stable `K_2`, and it gives no control of approximate
representations or of block-multiplicity routers.  Thus it must not be used
to infer projective trace-square transfer.  The surviving obstruction is the
noncentral, same-reservoir transport/holonomy identified by
`schur-clock-router-has-maximal-projective-leak`, not a new stable scalar
arithmetic phase.

