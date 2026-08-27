---
rg: 2
id: exact-exhaustive-typed-cap-chain-no-go-proof
kind: route
title: Threshold one exhaustive profile and apply the full-support covariance firewall
target: full-support-factor-refutes-exact-exhaustive-typed-cap-chain
requires:
  - full-support-factor-forbids-cap-ranged-common-source-covariance
  - polar-correction-preserves-povm-covariance
---

By `(ETC2)`, choose `lambda` with `H=Y_m^*Y_m` nonzero.  There is
`epsilon>0` for which

```text
P=1_[epsilon,1](H)
```

is nonzero.  The first inequality in `(ETC1)` gives
`Y_c^*Y_c>=epsilon P` on `P`.  Set

```text
S_c=Y_cP(PY_c^*Y_cP)^(-1/2).
```

Then `S_c^*S_c=P`, while the range condition in `(ETC1)` gives
`S_cS_c^*<=q_(c,lambda_c)`.  Apply
`polar-correction-preserves-povm-covariance` with zero raw error to `(ETC3)`;
it gives `A_(c,x)S_c=S_cB_x`.  The projection `P` and partial isometries
`S_c` contradict
`full-support-factor-forbids-cap-ranged-common-source-covariance`.

For the normalized Fano candidate, iterating

```text
sum_lambda ||T_(c,lambda)Z||_2^2
 =tau(Z^*(sum_lambda q_(c,lambda)/4)Z)
 =||Z||_2^2
```

proves `(ETC4)`.  Expanding the right side of `(ETC6)` cancels adjacent
terms and leaves its displayed left side.  The Pauli calculation uses
`XZ=-ZX`; hence `[Z,q]=ZX` and its normalized squared HS norm is `1`.
