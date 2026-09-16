---
rg: 2
id: separable-ccr-algebras-are-quasidiagonal-proof
kind: route
title: Block-diagonal finite-rank truncations of a direct sum of compact representations commute asymptotically with the image
target: separable-ccr-algebras-are-quasidiagonal
requires: []
artifacts:
  - research/artifacts/bk-type-i-k0-embedding-equivalence-2026-09-16.md
---

Full proof: artifact §1, Lemma 1, steps 1--5.

1. For a compact operator `T` and finite-rank projections `Q_m ↑ 1` strongly,
   `||Q_m T − T|| → 0`.  Strong convergence is uniform on the norm-compact set
   `T(ball)`.  Taking adjoints, `||[Q_m, T]|| → 0`.
2. Fix a dense sequence `(a_k)` in `A`.  Choose `Q_{i,m} ↑ 1` on each `H_i`.
   Choose `m_n ≥ n`, increasing, with `||[Q_{i,m_n}, π_i(a_k)]|| < 1/n` for
   `i, k ≤ n`.  Put `P_n = (⊕_{i ≤ n} Q_{i,m_n}) ⊕ 0`.
3. Then:
   - `P_n` is increasing and of finite rank;
   - `P_n → 1` strongly, by dominated convergence on `Σ_i ||ξ_i||²`;
   - `||[P_n, π(a_k)]|| < 1/n` for `n ≥ k`, because everything is block
     diagonal.

   A `2||a − a_k||` estimate extends this to all of `A`.
4. `⊕ π_i` is faithful, so `A` is quasidiagonal.  Quasidiagonal algebras are
   stably finite.
5. For a CCR algebra, choose irreducible `π_{k,m}` with
   `||π_{k,m}(a_k)|| > ||a_k|| − 1/m`.  The direct sum is isometric on a dense
   set, hence faithful.  The spaces are separable, and CCR puts every image in
   the compacts.  A separable type I algebra with `T_1` spectrum is CCR, since
   its primitive quotients are simple type I, hence elementary (standard;
   numbering not re-checked).
