---
rg: 2
id: contracting-groups-bound-roots-at-periodic-points-proof
kind: route
title: Bad vertices are closed under descendants and a vertex with only bad children is bad, giving good paths; at a good periodic point the sections of roots are plain sections, eventually in the nucleus, and a torsion-free root pair repeats at most |N|^2 times; the product odometer computes its return sections explicitly
target: contracting-groups-bound-roots-at-periodic-points
requires: []
---

Lane proof (bh-free-16, 2026-09-19). Notation as in the claim.

## Step 1. Good paths (item 1)

For a vertex `v` with `a`-orbit length `c_v` and a letter `x`, let `e` be the length of the orbit of `x` under `h_v`.
Then `c_(vx) = c_v e`, and `h_(vx) = (a^(c_v))^e|_(vx) = (h_v^e)|_x`, because `a^(c_v)` fixes `v`.
- **Bad descends.** If `h_v` has finite order, so does `h_v^e`, and so does its section at the fixed letter `x`.
- **A bad-children vertex is bad.** Suppose every child of `v` is bad. Let `E` be the lcm of the orbit lengths
  `e_x`. Then `h_v^E` fixes every letter, and its section at `x` is `h_(vx)^(E/e_x)`, of finite order. An
  automorphism that fixes level 1 and has finite-order sections has finite order, so `h_v` is bad.
- **Conclusion.** The root is good, since `h_∅ = a`. Every good vertex has a good child, so König's lemma gives a
  good path. The lengths `c_n` divide one another by the first display.

## Step 2. Roots act as powers on each level

Let `k` be `m`-free and `r ∈ Aut(T_m)` with `r^k = a`.
- **Level quotients.** The level-`n` quotient of `Aut(T_m)` is an iterated wreath product of `S_m`. Its order has
  prime factors `<= m`, so `k` is invertible modulo the order of the image of `r`. Hence `r = r^(kk') = a^(k')` on
  level `n`, for some `k'`.
- **So `r` has the same orbits as `a` on every level.** In particular `r` fixes every vertex that `a` fixes.

## Step 3. The pigeonhole (item 2)

Let `ξ` be a good periodic point of `a`, with orbit length `c`, and put `b = a^c`. Then `b` fixes every `ξ_n`, and
`b|_(ξ_n)` has infinite order for all `n`.
- **Roots.** Let `r ∈ Γ` with `r^k = a`, `k` `m`-free. Then `t = r^c ∈ Γ` satisfies `t^k = b`. By Step 2 applied to
  `t` and `b`, `t` fixes every `ξ_n`, so `(t|_(ξ_n))^k = b|_(ξ_n)`.
- **Choosing a level.** Pick `n >= max(n(b), n(t))`. Then `B_k = b|_(ξ_n)` and `T_k = t|_(ξ_n)` both lie in `𝒩`,
  with `T_k^k = B_k` and `B_k` of infinite order.
- **The count.** Suppose two such `k ≠ k'` give the same pair `(B, T)`. Then `T^k = T^(k')`, so `T` has finite
  order and so does `B = T^k`, which is a contradiction. So distinct `k` give distinct pairs in `𝒩 × 𝒩`, and
  there are at most `|𝒩|^2` of them.

## Step 4. Item 3

- **Many roots.** If `Z[1/P] ↪ Γ` with `1 ↦ a` and `P` is infinite, then `a` has a `p`-th root in `Γ` for every
  `p ∈ P`. Infinitely many of these `p` are `> m`, hence `m`-free. By Step 3, `a` has no good periodic point.
- **Unbounded orbits.** Along a good path, the `c_n` are non-decreasing divisors of one another. If they were
  bounded, they would be eventually constant, equal to `c`. Then `a^c` would fix `ξ` and `a^c|_(ξ_n) = h_(ξ_n)`
  would have infinite order for all large `n`, and by descent (Step 1) for all `n`. So `ξ` would be a good
  periodic point. Hence `c_n → ∞`.

## Step 5. The product odometer (item 4)

- **The action.** `(u, v) ∈ Z^2` acts on `Z_3 × Z_2` by translation. On the first letter `(i, j)`, it writes
  `((i + u) mod 3, (j + v) mod 2)`, and its section is the translation by
  `(⌊(i + u)/3⌋, ⌊(j + v)/2⌋)`.
  - So the action is self-similar, and it is faithful because `Z^2 → Z_3 × Z_2` is injective.
  - Sections of `(u, v)` at level `n` have coordinates of size at most `|u|/3^n + 1` and `|v|/2^n + 1`. So
    `𝒩 ⊆ {−1, 0, 1}^2`, and the action is contracting.
- **Orbits and return sections.** The level-`n` quotient is `Z/3^n × Z/2^n ≅ Z/6^n`, where `(1,1)` has order
  `6^n`. So `c_n = 6^n` for every vertex. `a^(6^n) = (6^n, 6^n)` fixes `0^n`, and its section is
  `(6^n/3^n, 6^n/2^n) = (2^n, 3^n)`. These are pairwise distinct elements.
- **The orbit coding.** `C(λ) = a^λ 0 = (λ, λ)`, for `λ ∈ Z_6`, with radix 6 at each level.
  - On the digit cylinder `λ ≡ j (mod 6^n)`, the section of `C` is
    `μ ↦ ((j − j_3)/3^n + 2^n μ, (j − j_2)/2^n + 3^n μ)`, where `j_3 = j mod 3^n` and `j_2 = j mod 2^n`.
  - The linear parts `(2^n, 3^n)` differ for different `n`, so `C` has infinitely many sections.
- **Periods.** For a prime `ℓ ∤ 6`, the digits of `1/ℓ` have period `ord_ℓ(6)` in `Z_6`. In the product coding they
  have period `lcm(ord_ℓ(3), ord_ℓ(2))`. ∎

## Remarks

- **Why periodic points are the right case.** At a good periodic point, the return sections of `a` and of all its
  roots are plain sections of the fixed powers `a^c` and `r^c`. The nucleus bounds plain sections, not powers.
  Along a path with `c_n → ∞` the return sections are sections of the growing powers `a^(c_n)`, and Step 5 shows
  they can be unbounded.
- **Beyond contraction.** Step 3 uses only that, for each `g ∈ Γ`, the sections of `g` along `ξ` eventually lie in
  one finite set independent of `g`. It therefore applies to any self-similar group that is contracting along the
  single ray `ξ`.
