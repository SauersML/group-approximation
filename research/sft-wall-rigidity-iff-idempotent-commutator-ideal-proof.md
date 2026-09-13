---
rg: 2
id: sft-wall-rigidity-iff-idempotent-commutator-ideal-proof
kind: route
title: Triangular families on k^2, the line-pair analysis of two-dimensional families, and a square-zero splitting of the local tiling algebra
target: sft-wall-rigidity-iff-idempotent-commutator-ideal
requires: []
artifacts:
  - research/artifacts/quantum-rigidity-walls-and-commutator-ideal-2026-09-13.md
---

The artifact, Sections 0–3, gives the complete proof. Outline:

1. **Triangular families (Theorem 1).**
   - (Q1) forces the off-diagonal entry to be `λ(z)(s_a - t_a)`, vanishing off the difference set `Δ`.
   - (Q2) says `λ` is constant on `2D`-components of `Δ`.
   - (Q3) holds automatically, because the upper-right entry of the product telescopes to
     `λ(prod s - prod t) = 0`.
   - A disconnected `Δ` therefore gives a noncommuting family, and a connected `Δ` gives only conjugates of
     the diagonal one.
2. **All families on `k^2` (Theorem 2).**
   - Split sites carry an unordered pair of eigenlines, and two split sites commute iff the pairs agree.
   - The pair is constant on `2D`-components of the split set.
   - A noncommuting family has two components with different pairs. Reading one side on every component, and
     flipping the side on exactly those two, gives `T_1, T_2 ∈ Ω`, since each `D`-ball meets at most one
     component. Their difference set is those two components, which is not `2D`-connected.
3. **The commutator ideal (Theorem 3).**
   - If `J_D != J_D^2`, then `M = J_D/J_D^2` is a module over `LC(Ω × Ω)`, and so has a nonzero point
     localization at some `(T_1, T_2)` (Lemma 3.1, by compactness of the clopen filter).
   - The square-zero extension `C_D / J_D^2 -> LC(Ω)` splits (Lemma 3.2, lifting refining complete orthogonal
     idempotent families along the countable union of finite-dimensional pattern algebras).
   - A functional on the localization then defines a noncommuting triangular representation with diagonal
     `(T_1, T_2)`. By Theorem 1 its difference set is disconnected.
   - Conversely, a wall gives a triangular representation that kills `J_D^2` but not `J_D`.
4. **Filtered families (Corollary 3.3).** The associated graded kills `J_D`, so `J_D` acts nilpotently, and
   `J_D = J_D^m` then acts by zero.
5. **Equivalences.** 1⇔2 by Theorems 1 and 2; 1⇒3 by Theorem 3; 3⇒4 by Corollary 3.3; 4⇒1 by Theorem 1.
