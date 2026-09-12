---
rg: 2
id: ghb7-l2-betti-two-euler-proof
kind: route
title: Atiyah's Euler characteristic formula on the free cocompact CAT(-1) triangle complex, with b_1^(2) = 0 from property (T)
target: ghb7-l2-betti-two-is-orbifold-euler-characteristic
requires:
  - ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2
---

Notation as in `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`: `Y` is the
CAT(−1) triangle complex of CCKW Theorem 3.1, on which `G` acts with a triangle as
strict fundamental domain, and `H` acts freely, properly and cocompactly.

1. **Model.** `Y` is contractible and `H` acts freely and cocompactly, so `Y` is a
   finite-type model of `EH` and `b_k^(2)(H) = b_k^(2)(Y; N(H))`.
2. **Euler characteristic formula** (Atiyah; Lück, *L²-Invariants*, Theorem 1.35(2)):
   `χ(H\Y) = Σ_k (−1)^k b_k^(2)(Y; N(H))`.
3. **Degrees 0 and at least 3.** `b_0^(2)(H) = 0` because `H` is infinite (Lück,
   Theorem 1.35(8)). `b_k^(2)(H) = 0` for `k >= 3` because `Y` is 2-dimensional.
4. **Degree 1.** `H` has property (T) (finite index in `G`), so `H^1(H; π) = 0` for
   every unitary representation `π` (Delorme–Guichardet). With `π = ℓ²H`, the reduced
   first ℓ²-cohomology vanishes, and `b_1^(2)(H)` is its von Neumann dimension, so
   `b_1^(2)(H) = 0`.
5. **Degree 2.** Steps 2–4 give `b_2^(2)(H) = χ(H\Y)`, and the established cell count
   gives `χ(H\Y) = [G:H]·1381/2401`.
6. **The group `G`.** L²-Betti numbers are multiplicative under passage to a
   finite-index subgroup (Lück, Theorem 1.35(9)), so `b_k^(2)(G) = b_k^(2)(H)/[G:H]`.
   This gives `b_2^(2)(G) = 1381/2401`. It agrees with the orbifold Euler characteristic
   of the triangle of groups: `1/343 + 2/2401 − 3/7 + 1 = 1381/2401`.
7. **Nonzero cohomology.** `b_2^(2)(H) > 0` is the von Neumann dimension of the reduced
   cohomology `H̄^2(H; ℓ²H)`, so that space is nonzero. It is a quotient of
   `H^2(H; ℓ²H)`, which is therefore nonzero as well.

**Trust surface.** The three cited statements of Lück's book and Delorme–Guichardet
were not re-read from the sources in this lane. They are standard.
