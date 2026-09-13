---
rg: 2
id: a7a7a8-triangle-candidates-no-small-linear-representation-proof
kind: route
title: Module classification plus an integral trace-ideal Gröbner basis [1] in dimension 7
target: a7a7a8-triangle-candidates-no-small-linear-representation
requires: []
artifacts: [research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md, experiments/hyperbolic-triangle-search/linZ.py, experiments/hyperbolic-triangle-search/linZ_c1.out, experiments/hyperbolic-triangle-search/linZ_c234.out, experiments/hyperbolic-triangle-search/linZ_cal.out, experiments/hyperbolic-triangle-search/linD.py, experiments/hyperbolic-triangle-search/linD_d7c0_cands.out]
---

The full argument is in `research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md`,
§§1, 2 and 5.

1. **Reduction.** Replace `K` by its algebraic closure. A nontrivial `φ` is injective on the
   simple vertex groups.
2. **Dimension at most 6.** `A_8` has no faithful representation of dimension at most 6 when
   `char K ≠ 2`. This is ordinary character theory, and for `p = 3, 5` the recalled Brauer tables. So `φ` is
   trivial.
3. **Dimension 7, modules.**
   - For `char K ∉ {2, 3, 5, 7}` the representation theory is ordinary. The faithful 7-dimensional modules
     are `F^7 = 1 ⊕ 6` for `A_7` and the heart of `F^8` for `A_8`.
   - For `p = 3, 5` the same holds: the composition factors are forced, and semisimplicity follows from
     `H^1(A_7, F_p^7) = H^1(A_6, F_p) = 0`.
   - These modules are invariant under all automorphisms.
4. **Integral parametrisation.**
   - Fix `α = φ|_A`, the permutation module, and `t_0 = φ(q)^{e_1}`, a 7-cycle matrix.
   - Every `β = φ|_B` with `β(x_B) = t_0` equals `h β_1 h^{-1}` with `β_1 = π β_0 π^{-1}`, where `π` is an
     integral permutation matrix, and `h ∈ C(t_0)`.
   - Since `t_0` is regular over every field, `C(t_0)` is the ring of circulants `Σ c_i t_0^i`. Put `k = h^{-1} = Σ d_i t_0^i`.
   - Scalars and `J = Σ t_0^i` centralise `β_1(B)`, which justifies the normalisation `Σ c_i = 1`.
5. **Necessary equations.** `(φ(r)^{e_2}, φ(p)^{e_3})` is conjugate to the `A_8`-heart, so the traces of
   117 words equal the integer traces of the heart.
6. **Certificate.**
   - For all four candidates Singular returns the strong Gröbner basis `[1]` over `Z` (`linZ_c1.out`, `linZ_c234.out`).
     So `1` is a `Z[c, d]`-combination of the equations, and the system has no zero over any field.
   - This agrees with the independent eigenbasis computation over `Q(ζ_7)` (`linD_d7c0_cands.out`).
7. **Calibration** (`linZ_cal.out`). On a twisted literal `(A_7,A_7,A_7)` triple, which has a
   7-dimensional representation, the same code returns a rational basis other than `[1]` and an integral basis without integers.

**Trusted inputs.**
- Singular's strong Gröbner bases over `Z` and `Q`.
- The recalled small Brauer characters of `A_7` and `A_8` for `p = 3, 5`.
