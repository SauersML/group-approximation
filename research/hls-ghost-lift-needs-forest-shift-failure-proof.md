---
rg: 2
id: hls-ghost-lift-needs-forest-shift-failure-proof
kind: route
title: Push a ghost-rank class to the forest shift, identify its expansion by local ranks, and pull a vanishing tree-boundary class back through the exact maximal sequence
target: hls-ghost-lift-needs-forest-shift-failure
requires:
  - bernoulli-pattern-expansions-are-finite
  - bernoulli-assembly-injective-beyond-the-host
  - bernoulli-bc-splits-into-host-and-cylinder-comparison
  - bernoulli-shift-weak-k-equivalence-and-going-down
  - hls-ghost-projection-breaks-k-exactness
artifacts:
  - research/artifacts/bc-bernoulli-hls-ghost-lift-2026-09-13.md
---

The complete argument is in `research/artifacts/bc-bernoulli-hls-ghost-lift-2026-09-13.md`, Sections 1--2.

1. **Shape of Ŷ (Lemma 1.1).**
   - Each `x_n` is isolated with trivial stabilizer, so their orbits form an open set `U` with `C_0(U) ≅ c_0(N × G)`.
   - Nonzero boundary points are `D`-regular tree configurations.
   - `C_0(Ŷ \ {0})` is a separable subalgebra of HLS's `ℓ^∞(N; c_0(G))`.
2. **The projection (Lemma 1.2).** The induced Laplacian plus the identity off the support has spectrum in
   `{0} ∪ [min(ε, 1, D - 2√(D-1)), ∞)` at every point of `Ŷ`. So its kernel projection `p` lies in the ideal, has rank `1`
   at `x_n`, and vanishes on the boundary.
3. **Forest comparison (Lemma 2.1).**
   - `T_r^T` is injective, by ranks at finite forests.
   - CC's weak K-equivalence restricts to the forest summand and to `T`. Bönicke--Dell'Aiera 4.6 identifies `T_r^T` with
     assembly at `C_0(T \ {0})`.
4. **Counts (Lemma 2.2).**
   - Ranks at finite forests, and at `x_n` for large `n`, are counts of the forest part `m(y)` of `n(y)`.
   - Patterns carrying coefficients have bounded diameter, hence fewer vertices than the girth.
5. **Key step.** A cylinder combination `m` with zero tree-boundary class comes, by (H-K) and the exact maximal sequence,
   from `K_0(c_0(N, K)) = ⊕_n Z`. So its counts on `A_n` vanish for large `n`.
6. **Theorem.**
   - If `y|_T = T_r^T(m')`, then `m' = m(y)` by 3 and 4.
   - Then `0 = y|_(∂Y) = b_(m(y))`, so the counts on `A_n` vanish eventually, contradicting nonzero ranks. This gives
     item 3.
   - Cylinder classes restrict to forest cylinder classes, so item 1 follows.
   - Item 2 follows from locality.
