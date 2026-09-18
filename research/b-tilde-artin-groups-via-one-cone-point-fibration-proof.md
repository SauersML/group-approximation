---
rg: 2
id: b-tilde-artin-groups-via-one-cone-point-fibration-proof
kind: route
title: Normalize the two special points by an affine map, parametrize the conic by C^×, and fibre over the configuration of the strands and the puncture
target: b-tilde-artin-groups-via-one-cone-point-fibration
requires:
  - free-kernel-extensions-stay-in-the-permutational-class
  - euclidean-artin-toric-commensurability
  - aut-free-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Notation as in the target.

**1. `E° ≅ Conf_2(C) × N_B`.**
- `Aff(C) = {z ↦ αz + β}` acts on `E°` by `(c, x, y) ↦ (αc + β, αx + β, αy)`. It
  preserves the equations, since both sides of `y_k^2 = (x_k − c_1)(x_k − c_2)` scale
  by `α^2`.
- The projection `E° -> Conf_2(C)`, `(c, x, y) ↦ (c_1, c_2)`, is equivariant, and
  `Aff(C)` acts simply transitively on `Conf_2(C)`. So `E°` is the product of
  `Conf_2(C)` with the fibre over `(0, 1)`:
  `E°_(0,1) = {(x, y) : x ∈ Conf_n(C), x_k ≠ 0, y_k^2 = x_k(x_k − 1)}`.
- The conic `y^2 = x(x − 1)` is parametrized by `w ∈ C^×`:
  `x = (w+1)^2/(4w)`, `y = (w^2 − 1)/(4w)`, with inverse `w = 2(x − ½ + y)`.
  - `x_k = x_j` ⟺ `w_k + w_k^-1 = w_j + w_j^-1` ⟺ `w_k = w_j^(±1)`;
  - `x_k = 0` ⟺ `w_k = −1`.
- So `E°_(0,1) ≅ {w : w_i ≠ w_j^(±1), w_k ≠ −1}`, and `v = −w` identifies this with
  `N_B`.
- `Conf_2(C) ≅ C × C^×` has `π_1 = Z`.

**2. The bundle.** Let `π(c, x, y) = (c_1, x)`. It lands in `Conf_(n+1)(C)`, because
the `x_k` are distinct and differ from `c_1`.
- *Fibre.* Fix `p = (c_1, x)`. Then
  `Σ_p = {(c_2, y) : c_2 ≠ c_1, y_k^2 = a_k (x_k − c_2)}` with `a_k = x_k − c_1 ≠ 0`.
  - Each equation is a double cover of the `c_2`-line branched at `x_k` and at `∞`,
    and unbranched at `c_1`.
  - `Σ_p` is their fibre product over `C − {c_1}`: the `(Z/2)^n`-cover whose
    monodromy sends a small loop around `x_k` to the `k`-th basis vector `e_k`.
  - The branch points `x_k` are distinct and simple, so `Σ_p` is smooth. The `e_k`
    generate `(Z/2)^n`, so `Σ_p` is connected.
- *Local triviality.* For `p'` near `p`, choose a diffeomorphism `φ_(p')` of `C`,
  isotopic to the identity through a compactly supported isotopy depending
  continuously on `p'`, with `φ(c_1) = c_1'` and `φ(x_k) = x_k'`. This is the
  standard local trivialization of configuration spaces.
  - `φ` maps `C − {c_1}` to `C − {c_1'}`, sends small loops around `x_k` to small
    loops around `x_k'`, and preserves the labelled monodromy.
  - So it lifts uniquely, once base lifts are fixed, to a homeomorphism
    `Σ_p -> Σ_(p')`, continuous in `p'`.
  - This gives `π^-1(U) ≅ U × Σ_p`.
- *Rank.* Riemann--Hurwitz for the open curve gives
  `χ(Σ) = 2^n χ(C − {c_1, x_1..x_n}) + n·2^(n−1) = −n·2^n + n·2^(n−1) = −n·2^(n−1)`.
  `Σ` is a non-compact Riemann surface of finite type, so `π_1(Σ)` is free of rank
  `1 − χ = 1 + n·2^(n−1) >= 2`.

**3. B_A.**
- `Conf_(n+1)(C)` is aspherical with `π_1 = P_(n+1)`, so the homotopy sequence gives
  `1 -> π_1(Σ) -> π_1(E°) -> P_(n+1) -> 1`.
- `P_(n+1) ≤ B_(n+1) ≤ Aut(F_(n+1))`, by Artin's representation, and `Aut(F_(n+1))`
  lies in `B_A` (`aut-free-groups-satisfy-permutational-boone-higman`).
- Part 4 of `free-kernel-extensions-stay-in-the-permutational-class` gives
  `π_1(E°) = Z × π_1(N_B) ∈ B_A`. Closure under subgroups gives `π_1(N_B) ∈ B_A`.

**4. Artin groups.**
- For `Φ = B_n`, `P^∨ = Z^n` (from `e_i(u) ∈ Z`), and `Q^∨` is the `D_n` lattice.
- With `L = Z^n` and `v = e^(2πiu)`, the toric complement is exactly `N_B`.
- `euclidean-artin-toric-commensurability` gives `A(B̃_n) ∈ B_A`. ∎

**Comparison with Li--Roushon.** Their fibre has rank `3n·2^(n−1) + 1` over
`Conf_n(C^×)`; this fibre has rank `n·2^(n−1) + 1` over `Conf_(n+1)(C)`. No
local-triviality lemma beyond the configuration-space isotopy is needed.
