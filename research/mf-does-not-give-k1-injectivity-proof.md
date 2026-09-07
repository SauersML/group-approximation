---
rg: 2
id: mf-does-not-give-k1-injectivity-proof
kind: route
title: An AH limit is MF, and the component group is already computed
target: mf-approximation-does-not-give-k1-injectivity
requires:
  - stw59-simple-ah-non-k1-injective
artifacts:
  - research/artifacts/ah-k1-mf-bridge-2026-09-07.md
---

## Why sufficient

Each stage `A_i = Gamma(X_i, End E_i)` is a unital homogeneous algebra, so it
is a corner of `C(X_i) tensor M_(n_i)` and is subhomogeneous; evaluation at
points of `X_i` gives a separating family of finite-dimensional
representations, so `A_i` is residually finite-dimensional and therefore MF.
MF is closed under inductive limits of separable algebras
(Blackadar--Kirchberg), so `A` is MF.

A unital embedding of `A` in a norm matrix corona restricts to an injective
group homomorphism from `U(A)` into the unitary group of that corona, so
every countable subgroup of `U(A)` is an MF group.

The remaining two values are the target claim's own: `K_1(A) = 0` and `v`
outside `U_0(A)`, so `U(A)/U_0(A)` is nonzero while `K_1(A)` is zero, and
`K_1`-injectivity fails.
