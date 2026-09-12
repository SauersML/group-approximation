---
rg: 2
id: ghb7-kernel-degree-two-newton-block-proof
kind: route
title: Free conjugation orbits of noncommuting pairs put the regular representation into the Ad-module, where b_2^(2) > 0 gives nonzero H^2
target: ghb7-kernel-blocks-degree-two-newton-stability
requires:
  - ghb7-l2-betti-two-is-orbifold-euler-characteristic
  - ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2
---

Cohomology of `H` is computed from the cellular cochains of the finite complex `H\Y`:
`Y` is contractible with a free cocompact `H`-action, so its cellular chain complex is
a resolution of `Z` by finitely generated free `Z[H]`-modules.

1. **Trivial summand.** `b_2(H;Q) >= 1380` by the established kernel claim, so
   `H^2(H; C) ≠ 0`. The constants `C·1 ⊂ L²(M)` are `Ad`-invariant, and `L²(M)` splits
   as `C·1 ⊕ (L²(M) ⊖ C)`. Each cochain group `Hom_H(C_k(Y), π) = π^(n_k)` splits
   accordingly, so `H^2(H; C)` is a direct summand of `H^2(H; π)`.
2. **Orthonormal vectors.** For `g, k ∈ H` put `w_{g,k} = [σ_n(g) ⊗ σ_n(k)] ∈ M`.
   Because `σ` is an asymptotic homomorphism, `(σ_n(g') ⊗ σ_n(k'))^* (σ_n(g) ⊗ σ_n(k))`
   is within `o(1)` in 2-norm of `σ_n(g'^{-1}g) ⊗ σ_n(k'^{-1}k)`. Its normalized trace
   is `τ(σ_n(g'^{-1}g)) · τ(σ_n(k'^{-1}k))`. By separation this tends to
   `δ_{g,g'} δ_{k,k'}`, so the `w_{g,k}` are orthonormal. Every `w_{g,k}` with
   `(g,k) ≠ (e,e)` is orthogonal to `1`.
3. **The action.** `Ad ρ_n(h)` sends `σ_n(g) ⊗ σ_n(k)` to
   `σ_n(h)σ_n(g)σ_n(h)^* ⊗ σ_n(h)σ_n(k)σ_n(h)^*`, which is within `o(1)` of
   `σ_n(hgh^{-1}) ⊗ σ_n(hkh^{-1})`. So `Ad ρ(h) w_{g,k} = w_{hgh^{-1}, hkh^{-1}}`, and the
   closed span of `{w_{g,k}}` is `ℓ²(H×H)` with diagonal conjugation.
4. **Free orbits.** `H` is torsion-free and hyperbolic, so the centralizer of each
   nontrivial element is infinite cyclic. If `x ≠ e` centralizes both `g` and `k`, then
   `g, k ∈ C_H(x)`, which is cyclic, so `g` and `k` commute. So a noncommuting pair has
   trivial stabilizer under diagonal conjugation. The closed span of its orbit is the
   left regular representation `ℓ²(H)`. `H` is non-elementary, so there are infinitely
   many such orbits, and `L²(M) ⊖ C ⊇ ℓ²(H) ⊗ ℓ²(N)`.
5. **Nonzero cohomology on the regular summand.** A Hilbert direct summand `V` of `π`
   gives `H^2(H; V)` as a direct summand of `H^2(H; π)`, by the splitting of step 1.
   `ℓ²(H)` is a direct summand of `ℓ²(H) ⊗ ℓ²(N)`. By
   `ghb7-l2-betti-two-is-orbifold-euler-characteristic`, `H^2(H; ℓ²H) ≠ 0`. So
   `H^2(H; π) ≠ 0` on a traceless summand.
6. **The method.** The Newton iteration corrects `σ` by a 1-cochain `y` with `δy = c`,
   where `c` is the relator-defect cocycle rescaled into `L²(M)`. Its input is vanishing
   of `H^2(H; π)`, with a modulus, for the `Ad`-modules of the asymptotic representations
   being rounded. Steps 1 and 5 show that input fails for `H`: on the trivial summand
   for every asymptotic representation, and on a regular summand for `σ ⊗ σ` whenever
   `H` is hyperlinear.
