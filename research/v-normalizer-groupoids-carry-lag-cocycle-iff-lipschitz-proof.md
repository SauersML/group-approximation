---
rg: 2
id: v-normalizer-groupoids-carry-lag-cocycle-iff-lipschitz-proof
kind: route
title: Synchronization makes the lag defect of conjugation by t depend only on k letters, and a length coboundary exists exactly on Lipschitz cores
target: v-normalizer-groupoids-carry-lag-cocycle-iff-lipschitz
requires:
  - v-normalizer-rsgs-contract-iff-finite-outer-order
artifacts:
  - research/artifacts/gq-gq-infinite-primes-out-v-reading.md
---

**Item 1.** `tVt^{-1} = V` gives `α_t(O) = O`. Every germ of `Γ_t` is `[v t^n, x] = [v, t^n x][t^n, x]`.
- If `[v t^n, x] = [v' t^{n'}, x]` with `n ≠ n'`, then `t^{n-n'}` agrees with an element of `V`
  on a neighbourhood of `t^{n'} x`, hence on a cone. By the Lemma in
  `v-normalizer-rsgs-contract-iff-finite-outer-order-proof`, `n = n'`, a contradiction.
- So `n` is determined by the germ, and the map `(g, n) ↦ g·[t^n]` from `O ⋊_{α_t} Z` is a
  bijective homomorphism onto `G_t`. It is a homeomorphism because the bisections
  `{[t^n, x]}` are open and compact, and the product is computed germwise.

**Item 2, the defect.** Let `k` be the synchronizing level of `t`, and for a word `z` let
`D(z) = |t̄(z)| - |z|`, where `t̄(z)` is the output read after input `z`. Let `v` replace a prefix
`u` by `u'`, and `x = uω`. For `n ≥ k` the core state reached after `u ω_1 … ω_n` equals the one
after `u' ω_1 … ω_n`, since it depends on the last `k` letters. So `t v t^{-1}` acts near `tx`
as the prefix replacement `t̄(u ω_1…ω_n) → t̄(u' ω_1…ω_n)`, and

    ℓ(α_t[v, x]) - ℓ([v, x]) = D(u ω_1…ω_k) - D(u' ω_1…ω_k).

A cocycle `c` extending `ℓ` with `c([t], x) = -κ(x)` exists iff the right side equals `κ(x) - κ(vx)`
for all such `v, x`. This is the compatibility condition for extending across the semidirect
product of item 1. Continuity forces `κ` to depend on a bounded prefix.

**Lipschitz ⇒ extension.** The Lipschitz constraint says the excess `|λ(q,a)| - 1` sums to 0 around
every circuit of the core. So it is a coboundary: `|λ(q,a)| - 1 = h(q·a) - h(q)` for some `h` on core
states. For `|z| ≥ k` put `K(z) = D(z) - h(q(z))`. Then `K(za) = K(z)`, so `K(z) = K(z_1 … z_k)`. Now
`D(u ω_1…ω_k) - D(u' ω_1…ω_k) = K(uω_1…ω_k) - K(u'ω_1…ω_k)`, since the two core states agree. That is
`K_t(x_{1..k}) - K_t((vx)_{1..k})`. So `κ = K_t` works, and it is locally constant.

**Extension ⇒ Lipschitz.** Suppose some core circuit `γ`, a word read from a core state back to itself,
has net excess `e ≠ 0`. Take `u = γ^m` preceded by a synchronizing word `s`, `u' = s`, and
`x = s γ^m ω`. Then `D(s γ^m ω_1…ω_k) - D(s ω_1…ω_k) = m e + O(1)`, which is unbounded in `m`. A
continuous `κ` on the compact space `C` is bounded, so `κ(x) - κ(vx)` is bounded. So no continuous
extension exists. ∎
