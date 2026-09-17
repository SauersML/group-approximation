---
rg: 2
id: self-relaying-product-with-a-binary-identity
kind: route
title: Multiply by the identity on two symbols, let every active product site relay itself and every birth use the old donor
target: self-relaying-donor-covering-automata-reach-admissible-types
requires: []
artifacts:
  - experiments/self-relaying-parity-2026-09-17/check.py
---

Notation of the target. Let `τ` be strict and self-relaying of type `(z, b)`, with memory `M`, local rule `μ` and
donor map `d`. Put `L' = L × {0,1}`, `Z' = Z × {0}`, `B' = L' \ Z' = (B × {0,1}) ⊔ (Z × {1})`. So
`|Z'| = z` and `|B'| = 2b + z`.

**The automaton.** `τ' = τ × id`, that is `τ'(ℓ, e) = (τ(ℓ), e)`. Its local rule on `M` is
`μ'(u, v) = (μ(u), v(1))`. It commutes with `G`, and it is strict because `τ` is strict and `id` is bijective:
injectivity is coordinatewise, and if `y ∉ τ(L^G)` then `(y, e) ∉ τ'(L'^G)` for every `e`.

**Active outputs.** `μ'(u, v) ∈ B'` iff `μ(u) ∈ B` or `v(1) = 1`.

**Donor map.** For `(u, v)` with `μ'(u, v) ∈ B'`, define
- `d'(u, v) = 1` if `(u(1), v(1)) ∈ B'`;
- `d'(u, v) = d(u)` otherwise.

In the second case `u(1) ∈ Z` and `v(1) = 0`, so `μ'(u, v) ∈ B'` forces `μ(u) ∈ B` and `d(u)` is defined.

**(D1).** Let `(ℓ, e)` be a configuration and `g` a site with `τ'(ℓ, e)(g) ∈ B'`. In the first case the donor is `g`
and `(ℓ(g), e(g)) ∈ B'` by the case condition. In the second case the donor is `D_ℓ(g)`, and (D1) for `τ` gives
`ℓ(D_ℓ(g)) ∈ B`, hence `(ℓ, e)(D_ℓ(g)) ∈ B × {0,1} ⊆ B'`.

**Self-relaying, hence (D2).** Let `(u, v)` have `(u(1), v(1)) ∈ B'`. If `u(1) ∈ B`, then `μ(u) ∈ B` because `τ` is
self-relaying, so `μ'(u, v) ∈ B'`. Otherwise `v(1) = 1` and `μ'(u, v)` has second coordinate `1`, so it lies in `B'`.
In both cases `d'(u, v) = 1` by definition. So `τ'` is self-relaying, and (D2) holds with `g = h`.

**Types.**
- `z = 1`: `b' = 2b + 1` is odd.
- `z = 2`: if `b` is odd, `τ` is already of type `(2, b)` with `4 ∤ b`; if `b` is even, `b' = 2b + 2 = 2(b + 1)` with
  `b + 1` odd, so `4 ∤ b'`.

**Item 5 witnesses.** `β × id` on `(A × {rest, active})^G` has local rule `(u, v) ↦ (μ_β(u), v(1))` and donor `d ≡ 1`.
If `v(1) = active`, the output is active and the donor is `1`. So it is self-relaying.

**Check.** `experiments/self-relaying-parity-2026-09-17/check.py` builds random self-relaying donor-covering rules
over `C_n`, forms the product, and verifies (D1), (D2), self-relaying and the type exhaustively for small `n`. It also
finds a non-self-relaying rule where the inherited donor map of the product breaks (D2). Over `C_n` every injective
automaton is surjective, so the script does not test strictness. Strictness transfers by the two-line argument above.
