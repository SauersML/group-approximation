---
rg: 2
id: fpbs-kazhdan-weak-containment-preserves-weak-mixing
kind: claim
title: For a Kazhdan group every action weakly contained in a weakly mixing action is weakly mixing, so weak-containment transfer from weakly mixing actions never reaches actions with a Kronecker factor
distinct_from:
  weak-containment-is-blind-to-kazhdan-fixed-algebras: that shows weak containment preserves ergodicity of a Kazhdan subgroup, which concerns invariant vectors (one-dimensional trivial subrepresentations); this shows it preserves the absence of every finite-dimensional subrepresentation of the reduced Koopman representation, and draws the cost-transfer consequence.
  amenable-rep-of-kazhdan-has-fd-subrep: that shows an amenable unitary representation of a Kazhdan group has a finite-dimensional subrepresentation; this shows that finite-dimensional subrepresentations of Koopman representations are inherited upward along weak containment of actions.
  fpbs-weakly-mixing-half-is-fixed-price-without-t: that is the non-(T) equivalence of P_w with fixed price; this is the obstruction that prevents the same argument for Kazhdan groups.
artifacts:
  - research/artifacts/fpbs-weakly-mixing-half-is-fixed-price-2026-09-17.md
---

**ESTABLISHED.** Let G be a countable group with property (T), and let a, c be p.m.p. actions of
G with a ≼ c. If c is weakly mixing, then a is weakly mixing. Equivalently, if κ^a_0 has a
nonzero finite-dimensional subrepresentation, then so does κ^c_0.

**Consequence (obstruction).** Suppose G is finitely generated with (T). Consider any argument
that proves C(a) ≥ C(b) for a free action a in two steps: first find a free action c with a ≼ c
and C(c) = C(b), then apply monotonicity of cost. If c is weakly mixing, as for every c controlled
by `fpbs-weakly-mixing-half-is-fixed-price-without-t` (its Corollary C), then the argument reaches
only weakly mixing a. It never reaches a nonergodic free action, or an ergodic free action with a
nontrivial Kronecker factor, such as a free profinite action of a residually finite Kazhdan group.
Without (T) the maximum is weakly mixing (`burton-kechris-maximum-action-weakly-mixing-without-t`),
and the transfer reaches everything. So the dividing line is exactly Burton-Kechris Theorem 3.20.

The proof is in artifact Section 4 (Theorem B). Let u_1, ..., u_n be an orthonormal basis of a
finite-dimensional σ ≤ κ^a_0. Zimmer weak containment κ^a_0 ≼_Z κ^c_0
(`burton-kechris-koopman-weak-containment`) gives w_i. Then η = Σ w_i ⊗ ū_i is almost invariant
for κ^c_0 ⊗ σ̄, with error at most 4(1+n)ε on F. Property (T) gives a nonzero invariant vector. That
vector is a Hilbert-Schmidt intertwiner S from σ to κ^c_0, and its range is a nonzero
finite-dimensional invariant subspace.
