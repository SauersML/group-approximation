---
rg: 2
id: leavitt-kazhdan-cover-rf-iff-kernel-rf-proof
kind: route
title: Split the acyclic simple quotient off every finite image, then trap a finite-residual element in a cyclic centralizer
target: leavitt-kazhdan-cover-rf-iff-kernel-rf
requires:
  - acyclic-quotientless-extension-completion-is-kernel-completion
  - binary-leavitt-unit-group-integrally-acyclic
  - binary-leavitt-unit-group-is-simple
  - openai-nine-leaf-leavitt-configuration
  - hyperbolic-kazhdan-cover-of-leavitt-unit-group
  - belegradek-osin-rips-construction
artifacts:
  - research/artifacts/hyperbolic-no-finite-quotient-leavitt-cover-2026-09-12.md
---

The full proof is in §2 of the artifact.

1. **Quotient.** `R^x` is integrally acyclic, so it is perfect with `H_2 = 0`
   (`binary-leavitt-unit-group-integrally-acyclic`). It is infinite and simple,
   hence without nontrivial finite quotient
   (`binary-leavitt-unit-group-is-simple`).
   `acyclic-quotientless-extension-completion-is-kernel-completion` gives items
   1 and 2, and `R_f(G) ∩ N = R_f(N)`.
2. **Instance.** In the Belegradek--Osin cover, `N` is a quotient of the
   finitely generated lattice. `G` is torsion-free because the lattice is
   (`belegradek-osin-rips-construction`, "Moreover" clause;
   `hyperbolic-kazhdan-cover-of-leavitt-unit-group`).
3. **Residual finiteness.** If `G` is residually finite, so is `N`.
   Conversely, let `N` be residually finite and suppose `1 ≠ g ∈ R_f(G)`.
   - Then `[g, N] ⊆ R_f(G) ∩ N = R_f(N) = 1`, so `N <= C_G(g)`. In a
     torsion-free hyperbolic group that centralizer is infinite cyclic
     (standard).
   - `N ≠ 1`: otherwise `G ≅ R^x`, but `R^x ⊇ V ⊇ Z^2`
     (`openai-nine-leaf-leavitt-configuration`), so it is not hyperbolic.
   - So `N ≅ Z` is normal in `G`. A subgroup of index at most 2 centralizes a
     generator of `N`, hence is cyclic, so `G` is virtually cyclic. That
     contradicts `G ->> R^x ⊇ Z^2`.

   Hence `R_f(G) = 1`.
