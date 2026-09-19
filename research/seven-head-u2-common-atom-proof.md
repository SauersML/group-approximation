---
rg: 2
id: seven-head-u2-common-atom-proof
kind: route
title: Refine the seven-head source and range by the remaining Pauli sign
target: seven-head-return-shares-sixteenth-atom-with-u2
requires:
  - seven-head-star-return-retains-eighth-flag
  - marked-star-outer-corrected-whiteheads-are-quarter-swaps
---

The first head satisfies the same conjugation formula on the previously
unused first Pauli sign as the later heads do on theirs:

```text
Ad(H_1)(Z_1)=Z_2C_1Z_1,
Ad(H_1^(-1))(Z_1)=C_1Z_1.                             (1)
```

This follows directly from `[A_1,B_1]=C_1`, followed in the forward
direction by `Ad(B_2)(C_1)=Z_2C_1`.  The other heads fix `Z_1` except
through the transported factors already appearing in `(1)`.

Substitution through `R_8=H_3H_2H_1H_2H_1H_2H_1` gives

```text
Ad(R_8)(Z_1)=C_1C_3Z_1Z_3Z_4.                        (2)
```

On the source support of `seven-head-star-return-retains-eighth-flag`,
the centers satisfy `C_1=C_3=-1` and `Z_3=Z_4=+1`.  Hence `(2)` reduces to
`Ad(R_8)(Z_1)=Z_1`, proving `(SCA2)` for either sign.

By the literal cell-swap formula for `U_2`, its adjoint action fixes
`Z_1,Z_4`, exchanges `Z_2,Z_3`, and preserves `E_4`.  It therefore maps
the sign pattern

```text
(Z_1,Z_2,Z_3,Z_4)=(epsilon,-,+,+)
```

to

```text
(epsilon,+,-,+),
```

which proves `(SCA3)`.  Equations `(SCA4)--(SCA5)` are then ordinary
finite-dimensional partial-isometry algebra.  Pauli balance for the four
cross-commuting cells gives `tau(P_epsilon)=tau(E_4)/16`; the positive
lower bound on `tau(E_4)` comes from the prerequisite four-cell star
overlap.
