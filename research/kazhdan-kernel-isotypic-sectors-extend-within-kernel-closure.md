---
rg: 2
id: kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure
kind: claim
title: Over a Kazhdan kernel whose quotient has no finite quotients, the group acts on bounded-multiplicity isotypic sectors inside the kernel closure
distinct_from:
  kazhdan-bounded-unitary-types-are-finite: that is Wang's finiteness of irreducible types in each dimension; this uses it to show that an extension by a group without finite quotients fixes every finite-dimensional type of the kernel, and acts on bounded-multiplicity isotypic sectors through the closure of the kernel.
  kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient: that shows the ambient group fixes the invariant block algebra of the kernel in sofic approximations; this is a representation-theoretic statement about every finite-dimensional isotype of the kernel, in any unitary representation.
artifacts:
  - research/artifacts/rnorm-kazhdan-projection-sizes-2026-09-12.md
---

**ESTABLISHED.** Let `1 -> N -> G -> Q -> 1` be exact, with `N` Kazhdan and
`Q` finitely generated with no nontrivial finite quotient. Let `pi` be a unitary
representation of `G` on a Hilbert space `H`; no separability is needed. For a
finite-dimensional irreducible unitary representation `rho` of `N` on `V_rho`,
write `W_rho = Hom_N(V_rho, H)`. This is the range of the Kazhdan projection of
`rho-bar (x) pi|_N`. Write `H_rho = V_rho (x) W_rho` for the isotypic subspace
and `P_rho` for its projection.

1. **Types are fixed.** Each `Irr_d(N)` is finite, and `rho o Ad(g) ~ rho` for
   every `g in G` and every finite-dimensional irreducible `rho`.
2. **Sectors are invariant.** `pi(G)` commutes with every `P_rho`.
3. **Outer part is inner.** On `H_rho`, `pi(g) = U_rho(g) (x) W_rho(g)`. Here
   `U_rho(g)` lies in the norm closure of `T . rho(N)`, and `W_rho` is a projective
   unitary representation of `G` that is trivial on `N`.
4. **Bounded multiplicity forces scalars.** Let `A` be an abelian von Neumann
   algebra on `H` commuting with `pi(G)`, so that `A|_(H_rho) = 1 (x) A_rho`.
   Let `E <= W_rho` be closed, invariant under `A_rho` and `W_rho(G)`, with
   `A_rho|_E` of multiplicity at most `m < infinity`.
   - `W_rho(g)|_E` is a scalar for every `g in G`.
   - For every finite family `S = (+)_i V_(rho_i) (x) E_i` of such sectors,
     `pi(g)|_S` lies in the norm closure of `T . pi(N)|_S`.

Derivation: `kazhdan-isotypic-sectors-kernel-closure-proof`.

**Sharpness.**
- **Finite quotients.** For `G = N x F` with `F` finite and nontrivial, and
  `pi = 1 (x) lambda_F`, `W_1 = lambda_F` is not scalar at multiplicity `|F|`.
- **Unbounded multiplicity.** For the quasi-regular representation
  `pi = l^2(G/N)` with `A = C`, `W_1 = lambda_Q` is not scalar at infinite
  multiplicity.

**Instance.** `hyperbolic-kazhdan-cover-of-leavitt-unit-group`, with
`Q = L_(F_2)(1,2)^x`, which is finitely presented and infinite simple. The
consequence for relative normalization is
`bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`.
