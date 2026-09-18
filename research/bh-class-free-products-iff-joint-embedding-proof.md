---
rg: 2
id: bh-class-free-products-iff-joint-embedding-proof
kind: route
title: Free products of subgroups inject, and U * U embeds in U * Z by conjugating the second factor
target: bh-class-free-products-iff-joint-embedding-and-free-z
requires:
  - fp-simple-groups-have-the-joint-embedding-property
---

Standard normal-form facts, not re-read at source: a free product of injective
homomorphisms is injective, and a word is trivial in a free product only if its
reduced form is empty.

**(FP) ⇒ (JE).** For finitely presented simple `S, T`, (FP) puts `S * T` inside
a finitely presented simple `U`, which contains `S` and `T`.

**(FP) ⇒ (FZ).** `U ∈ 𝓑`, and `Z ∈ 𝓑` (Thompson's group `T` contains `Z`). Apply (FP).

**(JE) ∧ (FZ) ⇒ (FP).** Let `G <= S` and `H <= T` with `S, T` finitely presented
simple. By (JE) choose `U` with `S, T <= U`. Then `G * H <= U * U`, because a free
product of injections is injective. Define `θ: U * U -> U * <t>` as the identity
on the first factor and `u ↦ t u t^{-1}` on the second. A reduced alternating word
`u_1 u'_1 u_2 u'_2 ...` (with `u_i` from the first factor and `u'_i` from the
second, all nontrivial) maps to `u_1 t u'_1 t^{-1} u_2 t u'_2 t^{-1} ...`, which is
reduced in `U * <t>` and so nontrivial. Hence `θ` is injective, and
`G * H <= U * Z ∈ 𝓑` by (FZ).

**Remark (products route).** For any `A, B`, the subgroup `<A x 1, t (1 x B) t^{-1}>`
of `(A x B) * <t>` is `A * B`, by the same normal-form argument. So if `A x B ∈ 𝓑`
and (FZ) holds for its envelope, then `A * B ∈ 𝓑`. ∎
