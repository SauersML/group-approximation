---
rg: 2
id: coset-graph-singular-values-bound-fixed-space-angles-proof
kind: route
title: Peter–Weyl identifies the coset graph spectrum with fixed-space angles in the irreducible representations
target: coset-graph-singular-values-bound-fixed-space-angles
requires: []
---

**Step 1: the operator `T` is `R_H R_K R_H`.** Write `R_H F(a) = |H|^{-1} Σ_{h ∈ H} F(ah)` for the
right-averaging projection onto the right-`H`-invariant functions `ℓ^2(A)^H`. Identify `ℓ^2(A/H)` with
`ℓ^2(A)^H` through `f ↦ F`, `F(a) = f(aH)`.
- `(Mf)(aH) = Σ_{x ∈ aH ∩ bK, bK} f(bK) = Σ_{h ∈ H} f(ahK) = |H| (R_H F)(a)`, where now `F(x) = f(xK)`.
- Likewise `(M^T g)(bK) = |K| (R_K G)(b)`, with `G(x) = g(xH)`.

So `T` acts on `ℓ^2(A)^H` as `R_H R_K R_H`. Rescaling the inner product on `ℓ^2(A/H)` by a constant does
not change eigenvalues. For orthogonal projections `P, Q`, the nonzero eigenvalues of `PQP` are the
squared singular values of `PQ`.

**Step 2: Peter–Weyl.** As an `A × A`-representation (left and right translation),
`ℓ^2(A) ≅ ⊕_{π ∈ Irr(A)} π ⊗ π^*`, and `R_H = ⊕_π 1 ⊗ P_{(π^*)^H}`. Hence the spectrum of `R_H R_K R_H` is
the union over `π` of the spectra of `P_{(π^*)^H} P_{(π^*)^K} P_{(π^*)^H}`, each with multiplicity `dim π`.
- The trivial `π` contributes the eigenvalue `1` once, on the constants.
- As `π` runs over `Irr(A)`, so does `π^*`.

Therefore `σ_2^2 = max_{π ≠ 1} ‖P_{π^H} P_{π^K}‖^2`, which is item 1.

**Step 3: arbitrary unitary representations.** Restrict `V` to `A` through the homomorphism.
- *Decomposition.* `V` is the orthogonal sum of its isotypic components `V_π ≅ π ⊗ C_π`, where `C_π` is
  a multiplicity Hilbert space. Each component is invariant, and `V^H = ⊕_π π^H ⊗ C_π`, and similarly for
  `K`.
- *The intersection.* Since `<H,K> = A`, `π^H ∩ π^K = π^A = 0` for `π ≠ 1`. So
  `V^H ∩ V^K = V_1 = V^A`.
- *The bound.* Let `u ∈ V^H` and `v ∈ V^K` be orthogonal to `V^A`, and write `u = Σ_{π≠1} u_π`,
  `v = Σ_{π≠1} v_π`. Then `u_π = P_{V^H} u_π` and `v_π = P_{V^K} v_π`, so
  `<u_π, v_π> = <u_π, (P_{π^H} P_{π^K} ⊗ 1) v_π>`. Its absolute value is at most
  `σ_2 ‖u_π‖ ‖v_π‖`.
- *Summing.* By Cauchy–Schwarz over `π`, `|<u, v>| <= σ_2 ‖u‖ ‖v‖`.

This is item 2. If one fixed space contains the other, there are no such nonzero vectors, and the cosine
is `0` by convention. ∎
