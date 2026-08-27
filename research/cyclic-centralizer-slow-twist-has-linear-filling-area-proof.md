---
rg: 2
id: cyclic-centralizer-slow-twist-has-linear-filling-area-proof
kind: route
title: Evaluate the cyclic centralizer presentation on a slowly rotating order-three block loop
target: cyclic-centralizer-slow-twist-has-linear-filling-area
requires: []
---

Let `omega=exp(2 pi i/3)`,

```text
D=diag(omega,omega^2),
B_theta=R_theta D R_theta^*,
```

where `R_theta` is the real two-dimensional rotation.  In Pauli notation,

```text
D=-(1/2)I+i(sqrt(3)/2)Z.
```

Direct calculation gives

```text
B_theta^3=I,
||B_theta-B_phi||_(2,2)=sqrt(3)|sin(theta-phi)|,
||[B_theta,B_phi]-I||_(2,2)
  =(3/2)|sin(2(theta-phi))|.                              (CST3)
```

Fix `j>=1`, set `N=8j`, and on

```text
H=C^N tensor C^2
```

put

```text
B=direct_sum_(k mod N) B_(2 pi k/N).
```

Let `C` cyclically shift the `N` blocks and act trivially inside each
two-dimensional block.  The cube relator is exact.  Unitary invariance and
the first difference formula in `(CST3)` give

```text
||[B,C]-I||_2
 =sqrt(3) sin(2 pi/N)
 =sqrt(3) sin(pi/(4j)).                                  (CST4)
```

The conjugate `C^(-j)BC^j` shifts the angle by

```text
2 pi j/N=pi/4.
```

The commutator formula in `(CST3)` therefore gives

```text
||[B,C^(-j)BC^j]-I||_2=3/2.                              (CST5)
```

If `q_j` is a product of `L` conjugates of the two defining relators and
their inverses, evaluation and telescoping bound its defect by the sum of
the evaluated cell defects.  Every `b^3` cell contributes zero and every
`[b,c]` cell contributes the value in `(CST4)`.  Hence

```text
3/2 <= L sqrt(3) sin(pi/(4j)),
```

which is `(CST2)`.  Since `sin x<=x`, one may take

```text
kappa=2 sqrt(3)/pi.
```
