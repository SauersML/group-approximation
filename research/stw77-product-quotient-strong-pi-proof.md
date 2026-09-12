---
rg: 2
id: stw77-product-quotient-strong-pi-proof
kind: route
title: Assemble uniform matrix diagonalizations and push them through arbitrary quotients
target: stw77-comparison-product-quotients-solve-map
requires:
  - stw78-simple-comparison-targets-force-oinfinity-stability
artifacts:
  - research/artifacts/stw77-map-oinfty-audit-2026-08-30.md
---

For each `lambda`, the coordinate map `P->B_lambda` is a unital quotient.
Proper infiniteness of `1_P` therefore makes `1_(B_lambda)` properly infinite.
The factor has no normalized `2`-quasitrace: two orthogonal subprojections of
the unit, each equivalent to the unit, would force

```text
1 >= tau(p_1+p_2)=tau(p_1)+tau(p_2)=2.
```

The simple almost-unperforated dichotomy used in
`stw78-simple-comparison-targets-force-oinfinity-stability` now makes every
`B_lambda` simple purely infinite, hence strongly purely infinite.

The passage to the product uses the uniform form of strong pure infiniteness.
Kirchberg--Sierakowski, Remark 3.2(i) in
[*Filling families and strong pure
infiniteness*](https://arxiv.org/abs/1503.08519), says that a C*-algebra `C`
is strongly purely infinite exactly when, for every `a,b in C_+`, `c in C`,
and `epsilon>0`, there are **contractions** `s,t in C` such that

```text
norm(s^* a s-a)<epsilon,
norm(t^* b t-b)<epsilon,
norm(s^* c t)<epsilon.                                    (2)
```

Fix `a=(a_lambda), b=(b_lambda) in P_+`, `c=(c_lambda) in P`, and
`epsilon>0`.  In each strongly purely infinite coordinate choose contractions
`s_lambda,t_lambda` satisfying (2) with tolerance `epsilon/2`.  The families

```text
s=(s_lambda)_lambda,   t=(t_lambda)_lambda
```

belong to `P` because their norms are uniformly at most one.  The norm in an
arbitrary C*-product is the supremum of the coordinate norms, so all three
errors in (2) for `s,t` are at most `epsilon/2`, and hence strictly below
`epsilon`.  Thus `P` is strongly purely infinite.  This is precisely where
the contraction version is needed; uncontrolled coordinate witnesses would
not define elements of the product.

Now let `q:P->Q=P/J` be any quotient and assume `Q` is nonzero.  Given
`a_bar,b_bar in Q_+` and `c_bar in Q`, choose positive lifts `a,b in P_+` and
an arbitrary lift `c in P`.  Apply (2) in `P` at tolerance `epsilon/2` and
put `s_bar=q(s)`, `t_bar=q(t)`.  These remain contractions, and quotient
contractivity gives

```text
norm(s_bar^* a_bar s_bar-a_bar) <= epsilon/2,
norm(t_bar^* b_bar t_bar-b_bar) <= epsilon/2,
norm(s_bar^* c_bar t_bar)       <= epsilon/2.
```

All three quantities are strictly below `epsilon`; hence the same
characterization makes `Q` strongly purely infinite.  This argument neither
lifts isometries from `Q` nor assumes that `J` is a coordinate ideal.

Finally, Gabe's Theorem 9.7 says that every nuclear homomorphism from a
separable exact domain into a strongly purely infinite codomain is strongly
`O_infinity`-stable.  Apply it to `Q`.  A finite-nuclear-dimensional map is
nuclear, so the LXXVII specialization follows without using pointwise proper
infiniteness of its range.
