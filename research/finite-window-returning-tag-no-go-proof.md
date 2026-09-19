---
rg: 2
id: finite-window-returning-tag-no-go-proof
kind: route
title: Project onto orbit constants and count the coweight boundary
target: finite-shell-window-cannot-wordize-returning-tag
requires:
  - shortest-second-denominator-return-has-coweight-holonomy
---

For each orbit `Omega_r`, let `J_r` be the projection onto its constant
line, and put `J=sum_r J_r`. Every actor permutation preserves each orbit
and commutes with `J`. The two off-diagonal `J_r`-blocks of the diagonal tag
have normalized squared norms

```text
(1/Q)(1-|bar_alpha_r|^2)                               (FSP1)
```

each. They cannot be cancelled by an operator commuting with `J`. Summing
the two blocks over `r` proves `(FSW3)`.

For the coweight statement, suppose `k^n gC=gC` for some `n!=0`. Then

```text
g^(-1)k^n g in SL_3(Z).                                (FSP2)
```

But the eigenvalues of `k^n` are

```text
2^n,        2^n,        2^(-2n).                      (FSP3)
```

For either sign of `n`, at least one is a rational noninteger. Every
eigenvalue of an integral matrix is an algebraic integer, and a rational
algebraic integer is an integer. This contradicts `(FSP2)`, so every
`k`-orbit in `X` is infinite.

For finite nonempty `F`, therefore `F!=kF`. Since the two sets have equal
cardinality, their symmetric difference has at least two points. On each
point of `F triangle kF`, exactly one of `A_F` and `kA_Fk^(-1)` has a
modulus-one diagonal coefficient. Restricting to `F union kF` gives the
first inequality in `(FSW6)`, and

```text
|F triangle kF|/|F union kF|>=2/(2|F|)=1/|F|          (FSP4)
```

gives the second.
