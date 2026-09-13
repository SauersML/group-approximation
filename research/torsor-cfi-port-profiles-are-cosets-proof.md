---
rg: 2
id: torsor-cfi-port-profiles-are-cosets-proof
kind: route
title: Compose quantum isomorphisms through the base graph and untwist the port contexts
target: torsor-cfi-port-profiles-are-cosets
requires:
  - torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra
artifacts:
  - research/artifacts/ex-kac-quantum-compiler-torsor-profiles-2026-09-13.md
---

The complete proof is §2 of the profiles artifact.

**Lemma E: `≅_t` is an equivalence relation on colored digraphs,
`t in {q, qa, qc}`.**
- **Reflexive.**  Use the identity magic unitary.
- **Symmetric.**  If `v_(xa) v_(x'a') = 0` then its adjoint
  `v_(x'a') v_(xa) = 0`.  So the transpose `w_(ax) = v_(xa)` is a
  colour-preserving magic unitary over `A^op`.  Finite-dimensional
  representations, tracial states and `R^U`-models pass to `A^op`, using
  conjugate spaces and the self-anti-isomorphism of `R^U`.
- **Transitive.**  `U_(xz) = sum_y v_(xy) (x) w_(yz)` is a magic unitary over
  `A (x) B`.
  - In `U_(xz) U_(x'z')` every surviving term has
    `c_X(x,x') = c_Y(y,y') = c_Z(z,z')`.
  - Finite-dimensional representations, tracial states and trace-preserving
    `R^U`-images are closed under tensor products, using
    `R^U (x̄) R^U ⊂ (R (x̄) R)^U ≅ R^U`.

**Lemma T: `A(Iso(Y_σ,Y_τ))` and `A(Iso(G_H(R',e), G_H(R',τσ^(-1))))` have the
same presentation.**  By
`torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra` both are coset
constraint algebras on the same contexts.
- A non-port context has `T_k = Stab(R'_k)` on both sides.
- A port context has `T = {τ_i σ_i^(-1)}` on both sides.

**Theorem.**
- **`N''_t` is a subgroup.**  It contains `e`.  If `δ, δ'` lie in it, then
  `G_H(R',δ) ≅_t G_H(R',δ')` by Lemma E, so `δ'δ^(-1)` lies in it by Lemma T.
- **`N_t` is a coset.**
  - If `σ, τ in N_t`, then `Y_σ ≅_t Y_τ`, so `τσ^(-1) in N''_t`.
  - If `σ in N_t` and `δ in N''_t`, then `Y_σ ≅_t Y_(δσ)` by Lemma T, so
    `δσ in N_t`.
  - Hence `N_t = N''_t σ_0`.
- **Boolean ports.**  `E = prod_i {e,t_i}` is an elementary abelian subgroup
  of `H^P`.  A coset of `N''_t` meets `E` in the empty set or in a coset of
  `N''_t ∩ E`.
  - `(-,+)(+,+)^(-1)(+,-) = (-,-)`, which gives the forbidden-sector
    statement.
