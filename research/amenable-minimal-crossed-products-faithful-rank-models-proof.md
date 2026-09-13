---
rg: 2
id: amenable-minimal-crossed-products-faithful-rank-models-proof
kind: route
title: Følner truncation of the orbit representation, with a private coordinate and syndetic visits for faithfulness
target: amenable-minimal-crossed-products-have-faithful-rank-models
requires: []
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
---

Complete proof: artifact Section 1 (Theorem F).

1. **Orbit representation.** On `k^(Γ)`, `ρ(f)δ_h = f(hx)δ_h` and `ρ(u_g)δ_h = δ_(gh)` define a unital representation.
2. **Truncation.** `ψ_n = P_(F_n) ρ(·) P_(F_n)` is linear and unital. Its multiplicativity defect has rank at most
   `Σ_(g∈K_b) |g F_n Δ F_n| = o(|F_n|)`, so it induces a unital homomorphism into the rank ultraproduct.
3. **Faithfulness.**
   - For `a = Σ_(g∈K) f_g u_g` with `f_(g_0) ≡ c ≠ 0` on `W'`, every `h` with `hx ∈ g_0^(-1)W'` has `ρ(a)δ_h` with
     coefficient `c` at `δ_(g_0 h)`.
   - Minimality and compactness give a finite `L` with syndetic visits, so at least `|F_n|/|L| - o(|F_n|)` such `h` lie in
     `F_n`.
   - A `K`-separated subset of them gives `rank ψ_n(a) >= |F_n| / (|L||K^(-1)K|) - o(|F_n|)`.
4. **Rank function.** Pull the normalized ultraproduct rank back; faithfulness passes to matrices. Rank ultraproducts are
   stably finite.
