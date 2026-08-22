---
rg: 2
id: kt-compressor-ultrapower-no-leak-proof
kind: route
title: No finite Lambda-orbits off the centre plus property (T) of the compressed copy give a uniform conjugation gap on the group factor
target: kt-compressor-pair-group-factor-ultrapower-has-no-leak
requires:
  - ccr-group-algebra-slice
---

Let `Lambda` act on `l^2(G) = L^2(L(G))` by conjugation,
`lambda . delta_g = delta_(lambda g lambda^-1)`, which is
`x -> u_lambda x u_lambda^*`.  The subspace `l^2(Z)` is pointwise fixed and
its orthocomplement `H = l^2(G) (-) l^2(Z)` is the orthogonal sum of the
permutation modules `l^2(O)` over the `Lambda`-conjugation orbits `O` of
non-central `g in G`.

**No invariant vectors.**  By `ccr-group-algebra-slice`,
`FC_Lambda(G) = Z`: every `Lambda`-orbit of a non-central element is
infinite.  A `Lambda`-invariant vector of `l^2(O)` is constant on the
infinite set `O` and square-summable, hence zero.  So `H` has no nonzero
`Lambda`-invariant vector.

**Property (T).**  `Lambda = EL_r(S) ~= EL_r(F_q[y_1..y_d])` with `r >= 3`
has Kazhdan's property (T) (Ershov--Jaikin-Zapirain, *Property (T) for
noncommutative universal lattices*, Invent. Math. 179 (2010), which covers
`EL_n(R)` for `n >= 3` and any finitely generated commutative ring `R`; the
uniform version for almost-representations is `el-r-polynomial-robust-spectral-gap`).
Hence there are a finite `S_0 subset Lambda` and `kappa > 0` with

```text
max_(s in S_0) ||s . xi - xi||  >=  kappa ||xi||    for all xi in H.     (KTUP1)
```

**Ultrapower.**  Let `x = (x_k)_k` represent an element of
`L(Lambda)' cap L(G)^omega`: `sup_k ||x_k|| < infinity` and
`lim_omega ||u_lambda x_k - x_k u_lambda||_2 = 0` for all `lambda in Lambda`.
Decompose `x_k = z_k + y_k` with `z_k` the projection of `x_k` onto
`l^2(Z)` and `y_k in H`; the decomposition is `Lambda`-equivariant, so
`lim_omega ||s . y_k - y_k||_2 = 0` for `s in S_0` and `(KTUP1)` forces
`lim_omega ||y_k||_2 = 0`.  Thus `x = (z_k)_k in L(Z)^omega`.  Since
`L(Z) = Z(L(G))`,

```text
L(Z)^omega subseteq L(G)' cap L(G)^omega subseteq L(Gamma)' cap L(G)^omega
  subseteq L(Lambda)' cap L(G)^omega subseteq L(Z)^omega,
```

which is `(KTU1)`.  Fullness of `L(G)` modulo the centre is the case of a
central sequence.  For a general tracial `M supseteq L(G)`, the
decomposition `L^2(M) = L^2(L(G)) (+) K_M` is `Lambda`-invariant; the
`Lambda`-fixed vectors of the first summand are `L^2(L(Z))` by the exact
slice (or by the argument above), and these are `G`-fixed; so a
`Lambda`-fixed vector of `L^2(M)` is `Gamma`-fixed iff its `K_M`-component
is, which is `(KTU2)`.
