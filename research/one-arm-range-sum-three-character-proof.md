---
rg: 2
id: one-arm-range-sum-three-character-proof
kind: route
title: Put the fixed arms globally and control only their complementary Pauli arms
target: one-arm-range-sum-whitehead-has-marked-model
requires:
  - payload-range-sum-whitehead-has-three-character-model
---

Use the three signs and character permutations from the preceding model:

```text
J  =diag( 1,-1,-1),
C_0=diag(-1,-1, 1),
C_1=diag(-1, 1,-1),                                   (1)
```

with `W_0=(0 2)`, `W_1=(0 1)`.  Thus

```text
C_0C_1=J,                  W_iJW_i^(-1)=C_i.           (2)
```

On `H=C^3 tensor C^2 tensor C^2`, let `P=(1-J)/2` and let
`x_i,z_i` be the Pauli `X,Z` on factor `i`.  This time put the first arms on
the whole space:

```text
X_i=I_(C^3) tensor x_i,
Z_i=(1-P)+P z_i.                                      (3)
```

Here the omitted Pauli factor in each tensor expression is the identity.
Since every `W_i` acts only on `C^3`,

```text
W_iX_iW_i^(-1)=X_i.                                   (4)
```

On `(1-P)H`, the commutator `[X_i,Z_i]` is one; on `PH` it is the Pauli
commutator `-1`.  Therefore

```text
[X_i,Z_i]=J.                                          (5)
```

The different-factor pairs commute.  Let

```text
P_i=W_iPW_i^(-1)=(1-C_i)/2,
Z_i'=W_iZ_iW_i^(-1)=(1-P_i)+P_i z_i.                  (6)
```

Using `(4)`, the same controlled-Pauli calculation gives

```text
[X_i,Z_i']=C_i.                                       (7)
```

Equations `(2)`, `(4)`, `(5)`, and `(7)` prove all of
`(OAR1)--(OAR2)`.  The prescribed projection `P` has rank eight and both
`X_i|_(PH)` are non-scalar Pauli arms, so the individual-arm authentication
is genuine on the selected atom.

All prototype discrepancies vanish in this exact model while the marked
atom survives.  Hence they cannot imply `(BAC1)`: otherwise zero prototype
defect would produce an exact binary Leavitt family in the nonzero finite
corner `PM_12(C)P`, contradicting the Atomic Leavitt Gap already used in the
preceding claim.
