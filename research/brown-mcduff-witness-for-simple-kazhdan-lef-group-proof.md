---
rg: 2
id: brown-mcduff-witness-for-simple-kazhdan-lef-group-proof
kind: route
title: Proof — ICC, Ozawa's Proposition 7.1 and a tensor with R give the McDuff witness; Kirchberg's Corollary 1.2 excludes U(R)
target: brown-mcduff-witness-for-simple-kazhdan-lef-group
requires: [simple-kazhdan-lef-group-from-minimal-subshift, infinite-simple-groups-are-icc, kazhdan-groups-in-hyperfinite-unitary-group-are-rf]
artifacts:
  - research/artifacts/sk-operator-algebras-proposal-2026-09-13.md
---

By `simple-kazhdan-lef-group-from-minimal-subshift`, `S` is infinite, finitely generated, simple, Kazhdan and LEF, so it is hyperlinear.

**(a)**
- By `infinite-simple-groups-are-icc`, `S` is ICC, so `L(S)` is a separable II_1 factor.
- Ozawa, *About the QWEP conjecture*, arXiv:math/0306067v1, Proposition 7.1 (source, verbatim): "A group $\G$ is
  hyperlinear if and only if $L\G$ is $*$-isomorphic to a von Neumann subalgebra of $R^\omega$." So `L(S) ↪ R^ω`.
- `M = L(S) ⊗̄ R` is a separable II_1 factor, and `M ⊗̄ R ≅ L(S) ⊗̄ (R ⊗̄ R) ≅ M`. So `M` is McDuff (McDuff: a separable
  II_1 factor `N` is McDuff iff `N ≅ N ⊗̄ R`).
- `M ↪ R^ω`: compose `L(S) ⊗̄ R → R^ω ⊗̄ R → (R ⊗̄ R)^ω ≅ R^ω`.
  - The middle map sends `(x_n)_ω ⊗ y ↦ (x_n ⊗ y)_ω` on the algebraic tensor product. It is well defined because
    `‖x_n ⊗ y‖_2 = ‖x_n‖_2 ‖y‖_2`.
  - It is a trace-preserving *-homomorphism, so it extends to the von Neumann tensor product.
- `s ↦ λ_s ⊗ 1` is an injective homomorphism `S → U(M)`.

**(b)**
- By `kazhdan-groups-in-hyperfinite-unitary-group-are-rf`, a finitely generated Kazhdan subgroup of `U(R)` is residually finite.
- Its source: E. Kirchberg, Math. Ann. 299 (1994), 551–563, p. 552, read from the PDF:
  - Corollary 1.2 (ii): "There exists a faithful unitary representation from G into the hyperfinite II_1-factor".
  - "(iv)⇒(ii)⇒(i) are true in full generality".
  - Theorem 1.1: "A discrete group with property (F) and property T is residually finite."
- `S` is infinite and simple, so it is not residually finite. Hence no faithful `S → U(R)` exists.

**Scope.** Both parts use only hyperlinearity, simplicity and property (T) of `S`. They hold verbatim for every
infinite simple hyperlinear Kazhdan group.
