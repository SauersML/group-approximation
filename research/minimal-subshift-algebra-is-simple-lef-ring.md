---
rg: 2
id: minimal-subshift-algebra-is-simple-lef-ring
kind: claim
title: The algebraic crossed product of an infinite minimal subshift over a finite field is a finitely generated simple LEF ring
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
---

Let `q` be a prime power, `X` an infinite minimal subshift over a finite alphabet `A`, `T` the
shift, and `R = LC(X,F_q) ⋊_T Z` the algebraic crossed product: finite sums `sum_j f_j u^j` with
`f_j` locally constant and `u f u^(-1) = f o T^(-1)`. Then:

1. `R` is generated as a ring by `u`, `u^(-1)`, the letter cylinders `chi_[x_0=a]`, and, when `q` is
   not prime, a primitive element of `F_q`.
2. `R` is simple, with centre `F_q`.
3. `R` is LEF as a ring. There is an injective unital `F_q`-linear ring homomorphism
   `R -> prod_omega M_(N_k)(F_q)` into an algebraic ultraproduct of full matrix algebras. It comes
   from periodic words `w_k` whose cyclic windows of length `2k+1` are exactly the words of
   `L_(2k+1)(X)`.

Consequently `GL_n(R)`, and every finitely generated subgroup of it, embeds in an ultraproduct of
the finite groups `GL_(nN_k)(F_q)` and is LEF.

Credits.
- **Item 2 as a Steinberg-algebra case.** `R` is the Steinberg algebra over `F_q` of the transformation
  groupoid `Z ⋉ X`, via `chi_({n}×U) ↦ chi_(T^n U) u^n`. That groupoid is Hausdorff, ample, effective (the
  action is free) and minimal. The simplicity criteria:
  - **Complex coefficients.** Brown--Clark--Farthing--Sims, arXiv:1204.3127, Theorem 4.1 (`thm:alg_simple`).
    It is stated for the complex Steinberg algebra only.
  - **Arbitrary fields, `F_q` included.** Steinberg, arXiv:1408.6014, Corollary 3.6, read from the PDF (p. 10):
    "Let G be a Hausdorff ample groupoid and k a field. Then kG is simple if and only if G is effective and
    minimal."
  - **Also arbitrary fields.** Clark--Edie-Michell, arXiv:1403.4684, Corollary 4.6, read from the PDF (p. 7): "Let G
    be a Hausdorff, ample groupoid and R a commutative ring with identity. Then A_R(G) is simple if and only if G
    is effective and minimal, and R is a field."

  The proof route proves item 2 directly, over every field, and does not depend on these citations.
- **Item 3.** The periodic return-word models are the mechanism of Grigorchuk--Medynets' LEF theorem for
  topological full groups (arXiv:1105.0719, Theorem 2.6, PDF p. 5), in ring form.
