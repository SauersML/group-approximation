---
rg: 2
id: subshift-el3-models-explicit-kazhdan-constant-proof
kind: route
title: Apply the explicit EJZ bound to R_X and to the full matrix algebras of primitive return words
target: subshift-el3-models-explicit-kazhdan-constant
requires: [ejz-elementary-groups-explicit-kazhdan-constant, minimal-subshift-algebra-is-simple-lef-ring, finite-simple-groups-converge-to-simple-kazhdan-group]
---

1. **The group `G`.** `R` is generated as a ring by `u`, `u^(-1)` and the letter
   indicators `e_a` (`minimal-subshift-algebra-is-simple-lef-ring`, item 1). Since
   `q = 2` is prime, no scalar generator is needed. With `x_0 = 1` and these
   `d = |A|+2` generators, `Σ` is the set `Σ` of
   `ejz-elementary-groups-explicit-kazhdan-constant` for `n = 3`, and
   `2√(3n) = 6`. So `κ(G, Σ) >= c_d`.
2. **The models.** Take `y_k` of least period `N_k`. This is the primitive-root
   replacement of `finite-simple-groups-converge-to-simple-kazhdan-group-proof`,
   step 1, which gives `N_k >= 2k+2`.
   - The rotations of `y_k` are distinct, so products of the conjugates
     `P^i D(e_a) P^(-i)` give every diagonal matrix unit.
   - So `P`, `P^(-1)` and `D(e_a)` generate `M_(N_k)(F_2)`, and
     `EL_3(M_(N_k)(F_2)) = SL_(3N_k)(F_2)` (same route, step 2).
   - The images `Σ_k` are the EJZ set for this ring and these `d` generators, so
     `κ(SL_(3N_k)(F_2), Σ_k) >= c_d`.
   - That route was reviewed PASS in `ex-review-groups-2026-09-12-part8.md` §8.6
     and in `ex-pestov91-second-review-2026-09-13.md` (N5).
3. **Spectral gap.** Over `F_2` each `e_ij(s)` is an involution, so the set `Σ_k`
   is symmetric and `|Σ_k| <= 6(d+1)`.
   - Let `M = |Σ_k|^(-1) sum_{s∈Σ_k} λ(s)` on `ℓ^2(SL_(3N_k)(F_2))`. It is
     self-adjoint.
   - For a unit vector `v` orthogonal to the constants, `||sv − v||^2 = 2 − 2 Re<sv, v>`,
     so `<(I − M)v, v> = (2|Σ_k|)^(-1) sum_s ||sv − v||^2`.
   - The regular representation on the orthogonal complement of the constants has
     no invariant vectors, so `max_s ||sv − v|| >= c_d`.
   - So `<(I − M)v, v> >= c_d^2/(2|Σ_k|) >= c_d^2/(12(d+1))`.
4. **Numbers.** `d = 4`: `12√8 + 6 + 36√2 = 90.853...`, so `c_4 = 1/726.82... > 1/727`.
   With `12(d+1) = 60`, `c_4^2/60 > 1/(60·727^2) = 1/31711740 > 3·10^(-8)`.
5. **Convergence.** `(SL_(3N_k)(F_2), Σ_k) → (G, Σ)` in the space of marked groups
   is step 3 of `finite-simple-groups-converge-to-simple-kazhdan-group-proof`, at
   `q = 2`.
