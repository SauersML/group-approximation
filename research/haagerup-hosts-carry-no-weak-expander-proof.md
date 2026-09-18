---
rg: 2
id: haagerup-hosts-carry-no-weak-expander-proof
kind: route
title: A proper cocycle is a coarse embedding, and the expander Poincare inequality cannot be met by a coarse embedding with small fibres
target: haagerup-hosts-carry-no-weak-expander
requires: [thompson-v-has-haagerup-property, sft-topological-full-groups-have-the-haagerup-property]
---

The two required nodes supply the hosts. The theorem itself uses only the
definition of the Haagerup property, as it is used in those nodes. A countable
group `G` has it when it admits an affine isometric action on a real Hilbert
space `H`, with linear part `π` and cocycle `b`, such that
`{g : ||b(g)|| ≤ C}` is finite for every `C`. Those nodes also record that the
property passes to subgroups (Cherix--Cowling--Jolissaint--Julg--Valette).

Fix a finitely generated `M ≤ G`, a finite symmetric generating set `S`, and
the word length `|·|`. Restricting the action gives a proper cocycle `b` on
`M`.

## 1. The cocycle is a coarse embedding of `M`

The cocycle identity is `b(gh) = b(g) + π(g) b(h)`. It gives
`b(g) - b(h) = π(h) b(h^{-1} g)`, so

```text
||b(g) - b(h)|| = ||b(h^{-1} g)||.                                   (1.1)
```

- *Upper bound.* Write `h^{-1} g = s_1 ... s_k` with `k = d(g,h)` and
  `s_i ∈ S`. The cocycle identity and the triangle inequality give
  `||b(h^{-1} g)|| ≤ k · K_S`, where `K_S = max_{s∈S} ||b(s)||`. So `b` is
  `K_S`-Lipschitz.
- *Lower bound.* Put `ρ(r) = inf { ||b(k)|| : |k| ≥ r }`. It is
  nondecreasing. It tends to infinity: for every `C`, only finitely many `k`
  have `||b(k)|| ≤ C`, and each has finite length. By (1.1),
  `||b(g) - b(h)|| ≥ ρ(d(g,h))`.

## 2. No weakly embedded expander

Let `X_n`, `d`, `λ`, `f_n`, `L` and `s_n` be as in the claim. Put
`φ_n = b ∘ f_n : X_n → H`. By §1, every edge `xy` has
`||φ_n x - φ_n y|| ≤ L K_S`.

*Poincaré inequality.* Let `u : X → R` be a function with mean `ū`. Then

- `Σ_{x,y} |u(x) - u(y)|^2 = 2|X| Σ_x |u(x) - ū|^2`;
- `Σ_{edges xy} |u(x) - u(y)|^2 ≥ λ_1(X) Σ_x |u(x) - ū|^2`, since `λ_1` is
  the smallest nonzero eigenvalue of the Laplacian of a connected graph.

Apply both to each coordinate of `φ_n` in an orthonormal basis of the span of
its image, and sum. With `|E(X_n)| ≤ d|X_n|/2`, this gives

```text
(1/|X_n|^2) Σ_{x,y} ||φ_n x - φ_n y||^2
    ≤ (2/(λ |X_n|)) Σ_{edges} ||φ_n x - φ_n y||^2 ≤ d L^2 K_S^2 / λ =: A.   (2.1)
```

*Markov step.* By (2.1), at most half of the ordered pairs `(x,y)` have
`||φ_n x - φ_n y||^2 > 2A`. Choose `R` with `ρ(r)^2 > 2A` for all `r > R`.
This is possible because `ρ → ∞`, and `R` does not depend on `n`. By §1,
every pair with `d_M(f_n x, f_n y) > R` has `||φ_n x - φ_n y||^2 > 2A`. So at
least `|X_n|^2 / 2` ordered pairs satisfy `d_M(f_n x, f_n y) ≤ R`.

*Counting step.* Fix `x`. Every `y` with `d_M(f_n x, f_n y) ≤ R` lies in the
union of the fibres of `f_n` over the ball `B(f_n x, R)`. That ball has
`|B_M(R)|` points, and each fibre has at most `s_n` points. So

```text
|X_n|^2 / 2  ≤  |X_n| · |B_M(R)| · s_n,   i.e.   s_n / |X_n| ≥ 1 / (2 |B_M(R)|),
```

for every `n`. This contradicts `s_n / |X_n| → 0`. So `M` carries no weakly
embedded expander.

## 3. Hosts

By `thompson-v-has-haagerup-property` and
`sft-topological-full-groups-have-the-haagerup-property`, the Haagerup
property holds for `V`, and so for its subgroups `T` and `F`, and for every
topological full group of a one-sided irreducible shift of finite type. §2
applies to each of their finitely generated subgroups.

## 4. The escaping host

`F_2<x,y> → F_2[x]`, `y ↦ 0`, is a surjective ring map. It carries elementary
matrices to elementary matrices, so it maps `EL_3(F_2<x,y>)` onto
`EL_3(F_2[x])`. The latter is infinite: the elementary matrices `e_12(x^k)`
are pairwise distinct.

`elementary-group-property-t-over-free-algebras` gives `EL_3(F_2<x,y>)`
property (T). An infinite Kazhdan group is not Haagerup, and the Haagerup
property passes to subgroups. So no group containing `EL_3(F_2<x,y>)` is
Haagerup. By `char-two-laurent-linear-groups-satisfy-boone-higman`, `L^x` is
such a group.

§4 is a remark and is not needed for the theorem, so its inputs are not
listed in `requires`. ∎
