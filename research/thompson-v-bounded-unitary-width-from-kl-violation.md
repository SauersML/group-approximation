---
rg: 2
id: thompson-v-bounded-unitary-width-from-kl-violation
kind: route
title: A Kervaire--Laudenbach violation over V forces bounded compact unitary relator width
target: thompson-v-has-bounded-compact-unitary-relator-width
requires:
  - kl-violating-equation-over-thompson-v
  - kl-kernel-lies-in-the-compact-unitary-width-radical
---

The first prerequisite supplies a word `w` with nonzero `t`-exponent sum and an element `1 != a in V` that dies in
`(V * <t>)/<<w>>`. So `a` lies in the normal closure of `R u {w}` in `F(S u {t})`, through an identity with `A`
old-relator factors.

1. Part (A) of `kl-kernel-lies-in-the-compact-unitary-width-radical` evaluates that identity at a Gerstenhaber--Rothaus
   root.
2. This gives `a(U) in Cons_A(R(U))` for every `d` and every `U in U(d)^S`.

So `a` has bounded width with `K = A`, the number of old-relator factors in the identity.
