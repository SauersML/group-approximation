---
rg: 2
id: relator-adjunctions-degree-two-growth-proof
kind: route
title: Euler characteristic additivity for attached 2-cells, Atiyah's formula with (T), and the free conjugation orbit argument
target: relator-adjunctions-grow-degree-two-cohomology
requires: []
---

Notation as in the claim: `X` is a finite 2-dimensional `K(Γ,1)`, `Y = X ∪_R e²` is
aspherical, `Q = π_1(Y)`.

1. **Model.** `Y` is aspherical, so `Y` is a finite 2-dimensional `K(Q,1)` and its
   universal cover is a contractible free cocompact `Q`-complex. Hence `Q` is
   torsion-free and `χ(Q) = χ(Y)`.
2. **Euler characteristic.** Attaching a 2-cell along a loop adds no 0- or 1-cells, so
   `χ(Y) = χ(X) + |R|`.
3. **Degree one.** `Γ` has (T), so `H_1(Γ;Z)` is finite and `b_1(Γ;Q) = 0`. `Q` is a
   quotient of `Γ`, so it has (T) and `b_1(Q;Q) = 0`.
4. **Rational `b_2`.** `X` and `Y` are 2-dimensional `K(·,1)` complexes, so
   `χ(X) = 1 + b_2(Γ;Q)` and `χ(Y) = 1 + b_2(Q;Q)` by step 3. Step 2 gives
   `b_2(Q;Q) = b_2(Γ;Q) + |R|`. This is item 1.
5. **`Q` is infinite.** If `Q` were finite, the finite aspherical `Y` would have
   torsion-free finite fundamental group, so `Q = 1` and `Y` would be contractible,
   with `χ(Y) = 1`. But `χ(Y) = 1 + b_2(Γ;Q) + |R| >= 2`, since `R` is nonempty.
6. **L2 Betti numbers.** By Atiyah's formula on the finite free model,
   `χ(Y) = Σ_k (−1)^k b_k^(2)(Q)`.
   - `b_0^(2)(Q) = 0`, because `Q` is infinite.
   - `b_1^(2)(Q) = 0`, because `Q` has (T): `H¹(Q;ℓ²Q) = 0`, and `b_1^(2)` is the von
     Neumann dimension of reduced `H¹(Q;ℓ²Q)`.
   - `b_k^(2)(Q) = 0` for `k >= 3`, since `Y` is 2-dimensional.

   So `b_2^(2)(Q) = χ(Y) = 1 + b_2(Γ;Q) + |R| > 0`, the von Neumann dimension of the
   reduced cohomology `H̄²(Q;ℓ²Q)`. That space is nonzero, and it is a quotient of
   `H²(Q;ℓ²Q)`, which is therefore nonzero. This is item 2.
7. **Trivial summand.** The constants in `L²(M)` are `Ad`-invariant, and
   `L²(M) = C·1 ⊕ (L²(M) ⊖ C)` splits every cochain group `Hom_Q(C_k(Ỹ), π)`. So
   `H²(Q;C)` is a direct summand of `H²(Q;π)`, and it is nonzero by item 1.
8. **Regular summand.** This repeats steps 2–5 of
   `ghb7-kernel-degree-two-newton-block-proof` with `H` replaced by `Q`; only the listed
   properties of `Q` are used.
   - The classes `w_{g,k} = [σ_n(g) ⊗ σ_n(k)]` are orthonormal, by separation, and
     `Ad ρ(h) w_{g,k} = w_{hgh⁻¹, hkh⁻¹}` for `ρ = σ ⊗ σ`.
   - In a torsion-free hyperbolic group the centralizer of a nontrivial element is
     infinite cyclic. So a noncommuting pair has trivial stabilizer under diagonal
     conjugation, and its orbit span is `ℓ²(Q)`. Non-elementary `Q` has infinitely
     many such orbits, so `L²(M) ⊖ C ⊇ ℓ²(Q) ⊗ ℓ²(N)`.
   - `ℓ²(Q)` is a Hilbert direct summand, so `H²(Q;ℓ²Q)` is a direct summand of
     `H²(Q;π)`, nonzero by item 2. This is item 3.

∎

**Trust surface.** Step 6 uses Atiyah's Euler characteristic formula and the vanishing
facts in Lück, *L²-Invariants*, Theorem 1.35(2),(8), together with Delorme–Guichardet
for `H¹(Q;π) = 0`. These are the same standard imports as
`ghb7-l2-betti-two-euler-proof`, and they were not re-read in this lane. Step 8's
centralizer fact is standard for torsion-free hyperbolic groups. Steps 1–5 and 7 use
no external input.
