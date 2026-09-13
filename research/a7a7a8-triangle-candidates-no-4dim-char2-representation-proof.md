---
rg: 2
id: a7a7a8-triangle-candidates-no-4dim-char2-representation-proof
kind: route
title: Torus parametrisation, eigenvalue signs and trace-ideal Gröbner bases decide all 4-dimensional char-2 representations of the four candidates
target: a7a7a8-triangle-candidates-no-4dim-char2-representation
requires: []
artifacts: [research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md, experiments/hyperbolic-triangle-search/lin4.py, experiments/hyperbolic-triangle-search/lin4_cands.out, experiments/hyperbolic-triangle-search/lin4_cal.out]
---

The full argument is in `research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md`, §§2–4.

1. **Reduction to `K = F̄_2`.** A representation over `K` extends to the algebraic closure of
   `K`, and a nontrivial one stays nontrivial.
2. **Vertex modules.** A nontrivial `φ` is injective on the simple vertex groups. Faithful
   4-dimensional modules of `A_7` and `A_8` in characteristic 2 are `4` or `4*`, both defined over
   `F_2`. This comes from the list of 2-modular irreducibles `1, 4, 4*, 6, …`. That gives 8
   type triples.
3. **Eigenvalue matching.** Each edge generator must have equal characteristic polynomials from
   both sides. The artifact's sign identity shows that this forces `σ(G) = +1`, and then exactly two
   triples survive. For `G_2` and `G_4` no triple survives, which was checked for all 8 triples.
4. **Completeness of the parametrisation.** Fix `α` on `A` and put `t = α(q)^{e_1}`, which has 4 distinct
   eigenvalues. Every `β` on `B` with `β(x_B) = t` is `S H S'^{-1} β_0 (S H S'^{-1})^{-1}` with
   `H = diag(h_1,h_2,h_3,1)`.
5. **Necessary conditions.** A homomorphism `C -> GL_4` with `x_C -> H M H^{-1}` and `y_C -> N`
   must be conjugate to `ρ_{ε_C}`. So traces of the 117 listed words in `(u,v)` equal those of
   `ρ_{ε_C}`.
6. **Certificate.** For `G_1` (triples `(4,4,4*)` and `(4*,4*,4)`) and for `G_3` (triples
   `(4,4,4)` and `(4*,4*,4*)`), Singular returns the Gröbner basis `[1]`. So the equations have no
   common zero over `F̄_2`.
7. **Calibration.** The same code finds the known representations of a literal
   `(A_8,A_8,A_8)` triple and of a twisted `(A_7,A_7,A_7)` triple with `e = (3,5,2)`. It reports
   0-dimensional ideals whose `F_8`-points satisfy every relator of `C`.

**Trusted inputs.**
- Singular's Gröbner basis computation.
- The GAP isomorphism `A_8 ≅ SL(4,2)`.
- The recalled list of small 2-modular irreducibles of `A_7` and `A_8`.
