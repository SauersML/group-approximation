---
rg: 2
id: finite-affine-head-cannot-retain-old-commutant-density-proof
kind: route
title: Tensor one active affine orbit with growing regular Toeplitz quotients
target: finite-affine-head-cannot-retain-old-commutant-density
requires:
  - affine-s3-endpoint-permutes-active-atoms
  - toeplitz-head-tail-unital-self-embedding
---

Choose one active character of `D`.  Extending either character of its
order-two stabilizer and inducing to `C_aff` gives a three-dimensional
irreducible representation `eta` on which `J=-I` and whose `D`-spectrum is
exactly the three active characters.  Thus `A=I_3`.  Restricted to the
affine `S_3`, `eta` is either

```text
1 direct_sum Std             or             sgn direct_sum Std,
```

so

```text
dim End_(S_3)(eta)=2.                                      (1)
```

For every `n`, choose a multiplicative generator `zeta_n` of
`F_(2^n)^x`.  The assignment

```text
T -> F_(2^n),             x |-> zeta_n, y |-> zeta_n^(-1) (2)
```

is a surjective ring homomorphism: `F_2[zeta_n]=F_(2^n)` and `yx=1`.
It induces a surjection

```text
Gamma -> Q_n=EL_r(F_(2^n)).                               (3)
```

Let `lambda_n` be the left-regular representation of `Q_n`, inflated along
`(3)`, and represent `(FAH1)` on

```text
H_n=C^3 tensor ell^2(Q_n)                                 (4)
```

by `C_aff` on the first factor and `Gamma` on the second.  The two copies of
`S_3` agree, so the universal property of the amalgam gives `rho_n`.

The active mass is one.  On the other hand, the commutant of the left-regular
action has vector-space dimension `|Q_n|`, while `(1)` gives

```text
dim End_(Gamma x S_3)(H_n)=2|Q_n|.
```

Since `dim H_n=3|Q_n|`, its normalized adjoint density is

```text
2|Q_n|/(9|Q_n|^2)=2/(9|Q_n|).
```

The orders of `EL_r(F_(2^n))` tend to infinity, proving `(FAH2)` and the
claimed obstruction.
