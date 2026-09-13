---
rg: 2
id: one-compressor-wreath-exact-vertex-proof
kind: route
title: Put a random Gamma-invariant sign on the layered origin model and separate cosets by origin truncation
target: one-compressor-wreath-has-models-with-exact-origin-vertex
requires:
  - one-compressor-actor-models-with-exact-origin-vertex
  - monomial-ascending-hnn-coset-action-sofic
artifacts:
  - research/artifacts/hs-extension-one-compressor-wreath-exact-vertex-2026-09-13.md
---

The full derivation is in §§0–4 of the artifact. Here `Y = {0..N} × Q_0`, `k = N c_A^N`, and
`O(j, g) = {j} × ψ_j(Γ) g`.

1. **Permutations.** `γ` acts on `Y` by `(j, g) -> (j, ψ_j(γ) g)` and `A` by `(j, g) -> (j-1, g)`. So
   `σ_N(v) = P_(v̂)` and `P_(v̂) M_F P_(v̂)^* = M_(F∘v̂^(-1))`.
   - Lamp translates are diagonal and commute exactly. The root lamp commutes exactly with `π_N(Γ)`.
   - The remaining relations of `W_A` are those of `V`, which hold in `M` by the premise.
2. **Separability** (the truncation argument of the second premise).
   - Suppose `φ^i(δ) ≡ s (mod m_0^k)` with `s ∈ EL_r(φ^(i+b)R_+)`, and every entry of `φ^i(δ)` has degree `< k`.
   - Then those entries are truncations of entries of `s`. They lie in the monomial-spanned polynomial ring
     `φ^(i+b)R_+`, so `φ^i(δ) ∈ SL_r(φ^(i+b)R_+)`.
   - Suslin stability gives `SL_r(φ^(i+b)R_+) = φ^(i+b)(Γ)`. So `δ ∈ φ^b(Γ)`.
3. **Distinct orbits.** For `R <= j <= N-R`,
   `v̂^(-1)(j, g) = (j - a + b, ψ_(j-a)(γ)^(-1) g)`.
   - After equalizing `a` with `φ^(a - a_i)`, equal orbits force `ψ_(j-a)(γ_i^(-1)γ_(i')) ∈ ψ_(j-a)(φ^b Γ)`.
   - Step 2 then forces `x_i = x_(i')`, since the degrees stay below `c_A^N D < k`.
4. **Trace.**
   - A nontrivial element of `V` acts without fixed points for large `N`, so any diagonal matrix times it has
     trace `0`.
   - For lamp products, a random `F` gives mean `<= 2R/(N+1)` and variance `<= (m + 4R)/(N+1)`. In the window,
     `E[X_y X_(y')] ≠ 0` confines `y'` to `m|Q_0|` points.
   - Chebyshev and a union bound over configurations in a ball of radius `R_N -> ∞` (growing slowly) give one
     `F_N` that works for all of them.
5. **Conclusion.** `ρ` is a trace-preserving homomorphism `W_A -> U(M)` with `ρ_N|Γ = π_N` genuine.
