---
rg: 2
id: brin-thompson-nv-haagerup-iff-proper-modulo-triangular-proof
kind: route
title: "T_n has a finite automorphic core, so properness modulo T_n averages to properness"
target: brin-thompson-nv-haagerup-iff-proper-modulo-triangular
requires:
  - haagerup-iff-proper-mod-subgroup-with-finite-automorphic-core
  - brin-thompson-nv-product-subgroup-has-finite-shear-core
---

Notation is as in the target. `nV` is countable.

- *(1) ⇒ (2), (3), (4).* A proper cnd function is proper modulo every subgroup (item 3 of
  `haagerup-iff-proper-mod-subgroup-with-finite-automorphic-core`, "only if").
- *(3) ⇒ (2).* `V^n ≤ T_n` (item 1 of `brin-thompson-nv-product-subgroup-has-finite-shear-core`), so
  every left coset of `V^n` lies in a left coset of `T_n`, and a finite cover by cosets of `V^n`
  gives one by cosets of `T_n`.
- *(4) ⇒ (2) or (3).* If `ψ` is proper modulo `α(T_n)`, then `ψ ∘ α` is cnd and proper modulo
  `T_n`, by item 1 of `haagerup-iff-proper-mod-subgroup-with-finite-automorphic-core` applied to
  `α`. The same for `V^n`.
- *(2) ⇒ (1).* By item 3 of `brin-thompson-nv-product-subgroup-has-finite-shear-core` there are
  automorphisms `α_1, ..., α_r` of `nV` with `α_1(T_n) ∩ ... ∩ α_r(T_n)` finite. By item 3 of
  `haagerup-iff-proper-mod-subgroup-with-finite-automorphic-core` with `H = T_n`, a cnd function
  proper modulo `T_n` gives the proper cnd function `Σ_i ψ ∘ α_i^{-1}`, so `nV` has the Haagerup
  property. With `α_i = Ad(t^{-1}) ∘ α_σ` one has `α_i^{-1} = α_σ^{-1} ∘ Ad(t)`, which is the
  displayed formula. ∎
