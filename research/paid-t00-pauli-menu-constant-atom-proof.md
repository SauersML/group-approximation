---
rg: 2
id: paid-t00-pauli-menu-constant-atom-proof
kind: route
title: Average the paid discrepancy over the eight native Pauli character atoms
target: paid-t00-pauli-menu-hits-whitehead-constant-atom
requires:
  - native-t00-y1-collision-pays-marked-opnorm
  - middle-index-marked-heisenberg-packet-is-whitehead-equivariant
---

The marked root commutes with `D`, so `C=P(1-D)/2` is a projection.  The
eight projections in `(PAM1)` are orthogonal and sum to `P`.  Cyclicity and
positivity therefore give

```text
sum_epsilon tau(e_epsilon C e_epsilon)=tau(C).
```

By `(PAM3)`, one sign vector satisfies

```text
tau(e_epsilon C e_epsilon)>=tau(P)/(16*8)=tau(P)/128. (1)
```

On `PH`, each `Y_m` anticommutes with `X_m`, commutes with the other two
`X` generators, and commutes with `z`.  Products of the three literal
`Y_m` therefore act transitively on the eight atoms.  Conjugate `(1)` by the
word carrying `e_+` to `e_epsilon`.  This gives exactly `(PAM4)--(PAM5)`.

Put `A=e_+C_epsilon e_+`.  It is a positive contraction supported on `e_+`,
and `tau(e_+)=tau(P)/8`.  If `E=1_([1/32,1])(A)`, then

```text
tau(A)<=tau(E)+(1/32)tau(e_+)
      =tau(E)+tau(P)/256.
```

Combining this with `(PAM5)` proves `tau(E)>=tau(P)/256`.  Finally both
adjacent prefix Whiteheads permute the three Pauli coordinates and hence fix
the constant-sign atom.  All menu words are literal products of the named
middle-index roots, so the argument is occurrence-typed and independent of
the ambient matrix dimension.
