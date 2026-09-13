---
rg: 2
id: a7a7a8-triangle-candidates-no-small-linear-representation-proof
kind: route
title: Module classification plus torus parametrisation and trace-ideal Gröbner bases in dimension 7
target: a7a7a8-triangle-candidates-no-small-linear-representation
requires: []
artifacts: [research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md, experiments/hyperbolic-triangle-search/linD.py, experiments/hyperbolic-triangle-search/linD_d7c0_cands.out, experiments/hyperbolic-triangle-search/linD_d7p3_cands.out, experiments/hyperbolic-triangle-search/linD_d7p29_cands.out]
---

The full argument is in `research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md`,
§§1, 2 and 5.

1. **Reduction.** Replace `K` by its algebraic closure. A nontrivial `φ` is injective on the
   simple vertex groups.
2. **Dimension at most 6.** `A_8` has no faithful representation of dimension at most 6 in
   characteristic 0 or 3, 5, 11, 13, 29, 43 (ordinary and Brauer character tables of `A_8`,
   recalled). So `φ` is trivial.
3. **Dimension 7, modules.**
   - For `A_7` the faithful modules are `1 ⊕ 6`. Semisimplicity comes from
     `H^1(A_7, F_p^7) = H^1(A_6, F_p) = 0`, by Shapiro's lemma.
   - For `A_8` the faithful module is the 7-dimensional heart of the permutation module.
   - Each is unique up to isomorphism, including twists by automorphisms, since the
     permutation modules are `S_7`- and `S_8`-invariant.
4. **Torus parametrisation.** An element of order 7 has 7 distinct eigenvalues on these modules.
   Every `β` on `B` with `β(x_B) = t = φ(q)^{e_1}` is conjugate to `β_1` by an element of the
   diagonal torus in the eigenbasis of `t`. The diagonal matrices that are scalar on the summands `6` and `1`
   centralise both `β_1(B)` and `v = φ(p)^{e_3}`, because `t` lies in both `φ(A)` and `φ(B)` and
   so its eigenvectors lie in the summands. So the eigenvalue-1 and eigenvalue-`ω` coordinates are normalised to 1.
5. **Necessary equations.** They are the traces of 117 words in `u = φ(r)^{e_2}` and `v`, equated with those of the
   `A_8`-module `7`.
6. **Certificate.** For all four candidates Singular returns the Gröbner basis `[1]`. It does so over
   `Q(ζ_7)` and over `F_{p^k}` for `p = 3, 5, 11, 13, 29, 43`. So the equations have no common
   zero.
7. **Calibration.** On a twisted literal `(A_7, A_7, A_7)` triple and a literal `(A_8, A_8, A_8)`
   triple, which do have representations, the same code returns 0-dimensional ideals. Over
   `F_{3^6}` and `F_29` the points are verified on every relator of `C`.

**Trusted inputs.**
- Singular's Gröbner bases.
- The small-degree modular irreducibles of `A_8` for `p = 3, 5`.
