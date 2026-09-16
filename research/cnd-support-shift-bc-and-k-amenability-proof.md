---
rg: 2
id: cnd-support-shift-bc-and-k-amenability-proof
kind: route
title: Tu's dual-Dirac factorization through a proper algebra proves both assembly maps at a CND-support shift are isomorphisms, and max to reduced follows
target: cnd-support-shift-bc-and-k-amenability
requires:
  - cnd-support-shift-actions-are-a-t-menable
  - a-t-menable-actions-have-tu-dual-dirac-elements
  - bernoulli-shift-weak-k-equivalence-and-going-down
artifacts:
  - research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md
---

Full argument: `research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md`, Section 4.

1. **Dual-Dirac elements.**
   - `Z` is second countable and locally compact: it is closed in the open subset `X^0` of the compact metrizable `X`.
   - The action on `Z` is a-T-menable (`cnd-support-shift-actions-are-a-t-menable`, item 2).
   - By `a-t-menable-actions-have-tu-dual-dirac-elements` there are a proper `Z ⋊ G`-algebra `A`, `α ∈ KK^G(A, C_0(Z))`
     and `β ∈ KK^G(C_0(Z), A)` with `β ⊗_A α = 1`.
2. **Assembly at `A`.**
   - `A` is proper, so `mu_(r, A)` is an isomorphism (`bernoulli-shift-weak-k-equivalence-and-going-down`, item 3).
   - All crossed products of a proper algebra agree (`a-t-menable-actions-have-tu-dual-dirac-elements`, last sentence of
     the statement), so `(λ_A)_*` is an isomorphism.
   - Reduced assembly is maximal assembly followed by `(λ_A)_*` (context; BGW, proof of Proposition 4.5). So
     `mu_(max, A)` is an isomorphism too.
3. **Functoriality (context, Kasparov 1988; Baum--Connes--Higson 1994).** Write `x_*` for `K^top(x)` and `j(x)_*` for the
   product with the descended element, for either crossed product.
   - `α_* β_* = id` on `K^top_*(G; C_0(Z))` and `j(α)_* j(β)_* = id` on `K_*(C_0(Z) ⋊ G)`.
   - `mu_Z ∘ α_* = j(α)_* ∘ mu_A` and `mu_A ∘ β_* = j(β)_* ∘ mu_Z`.
4. **Items 1 and 2.** Fix either crossed product.
   - Surjective: for `v ∈ K_*(C_0(Z) ⋊ G)`, `v = j(α)_* j(β)_* v = j(α)_* mu_A(mu_A^(-1) j(β)_* v) = mu_Z(α_* mu_A^(-1) j(β)_* v)`.
   - Injective: if `mu_Z(u) = 0`, then `mu_A(β_* u) = j(β)_* mu_Z(u) = 0`. So `β_* u = 0`, and `u = α_* β_* u = 0`.
5. **Item 3.** `mu_(r, Z) = (λ_Z)_* ∘ mu_(max, Z)`, and both assembly maps are isomorphisms. So
   `(λ_Z)_* = mu_(r, Z) ∘ mu_(max, Z)^(-1)` is an isomorphism. No compatibility of `λ` with descent is needed. QED.

**Why KK and not E-theory.** BGW state (6.1) in E-theory, where descent to the reduced crossed product needs
exactness. Step 3 uses reduced descent over a possibly non-exact `G`. That is why the import is taken in Tu's KK form.
