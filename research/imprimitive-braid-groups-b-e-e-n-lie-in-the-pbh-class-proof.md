---
rg: 2
id: imprimitive-braid-groups-b-e-e-n-lie-in-the-pbh-class-proof
kind: route
title: Translate the configuration by a free parameter c, fibre over the strand positions c + y_k^e, and apply free-kernel permanence
target: imprimitive-braid-groups-b-e-e-n-lie-in-the-pbh-class
requires:
  - free-kernel-extensions-stay-in-the-permutational-class
  - aut-free-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
---

Notation as in the target.

**0. The arrangement.** The reflections of `G(e,e,n)` are `y_i ↔ ζ y_j` (swap
coordinates `i` and `j`, with a twist by `ζ^(±1)`), for `ζ^e = 1` and `i ≠ j`. There are
no diagonal reflections. So the reflecting hyperplanes are `{y_i = ζ y_j}`, and
`M = {y : y_i^e ≠ y_j^e for i ≠ j}`. `G(e,e,n)` acts freely on `M` with quotient map a
covering of degree `|G(e,e,n)| = e^(n−1) n!`, so `P(e,e,n)` has finite index in
`B(e,e,n)`.

**1. The total space.** Let `E = {(c, x, y) : x ∈ Conf_n(C), y_k^e = x_k − c}`. The maps
`(c, y) ↦ (c, c + y^e, y)` and `(c, x, y) ↦ (c, y)` are inverse homeomorphisms
`C × M ≅ E`, because `x_i ≠ x_j ⟺ y_i^e ≠ y_j^e`. So `π_1(E) = P(e,e,n)`.

**2. The bundle `π(c, x, y) = x`.**
- *Fibre.* `Σ_x = {(c, y) : y_k^e = x_k − c}`. Each equation is a cyclic `e`-fold
  cover of the `c`-line, totally ramified at `c = x_k` (and at `∞`).
  - `Σ_x` is their fibre product over `C`: the `(Z/e)^n`-cover whose monodromy around
    `x_k` is the `k`-th generator.
  - It is smooth: near `c = x_k`, `y_k` is a coordinate and `c = x_k − y_k^e`, while the
    other factors are unramified because `x_j ≠ x_k`.
  - It is connected, because the monodromies generate `(Z/e)^n`.
- *Local triviality.* For `x'` near `x`, take a compactly supported isotopy `φ` of `C`
  with `φ(x_k) = x_k'`, continuous in `x'`. It preserves the labelled monodromy, so it
  lifts to homeomorphisms `Σ_x -> Σ_(x')`, continuous in `x'`. (This is the argument
  of `b-tilde-artin-groups-via-one-cone-point-fibration-proof`, step 2.)
- *Euler characteristic.* Each `x_k` has `e^(n−1)` preimages, so
  `χ(Σ) = e^n χ(C − {x_1..x_n}) + n e^(n−1) = e^(n−1)(e − n(e−1))`.
  - For `e, n >= 2` this is `< 0` unless `(e, n) = (2, 2)`, where it is `0`.
  - `Σ` is a finite-type non-compact Riemann surface, so `π_1(Σ)` is free of rank
    `1 − χ(Σ)`, which is `>= 3` when `χ < 0`.

**3. B_A.**
- `Conf_n(C)` is aspherical with `π_1 = P_n`, so
  `1 -> π_1(Σ) -> P(e,e,n) -> P_n -> 1` is exact.
- `P_n ≤ B_n ≤ Aut(F_n) ∈ B_A` (Artin's representation;
  `aut-free-groups-satisfy-permutational-boone-higman`).
- For `(e, n) ≠ (2, 2)`, Part 1 of
  `free-kernel-extensions-stay-in-the-permutational-class` gives `P(e,e,n) ∈ B_A`.
- Closure under finite-index overgroups
  (`boone-higman-type-a-class-closed-under-finite-extensions`) gives
  `B(e,e,n) ∈ B_A`. It is finitely generated, so it embeds in a finitely presented
  simple group (`type-a-action-gives-boone-higman-for-subgroups`).
- For `(e, n) = (2, 2)`, `B(2,2,2) = A(A_1 × A_1) = Z^2 ∈ B_A`. ∎
