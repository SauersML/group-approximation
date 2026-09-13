---
rg: 2
id: archimedean-trace-pushouts-give-qd-killing-proof
kind: route
title: Kill on the trace-kernel corner by Schafhauser realisation, pull back over the quasidiagonal quotient, separate by positivity at projections, and glue
target: archimedean-trace-pushouts-give-qd-killing
requires: [separating-killing-quotients-give-faithful-qd-killing, moutzouris-faithful-trace-zero-class-both-signs, brown-dadarlat-qd-extensions-and-k0-hahn-banach]
artifacts:
  - research/artifacts/bk-rr0-trace-pushout-killing-part2-2026-09-13.md
---

Proposition R2 and Theorem D, §§2–3 of the artifact.

1. `N = ker σ ⊆ I_P`, and `σ̄` is faithful on `I_P/N`.  `I_P/N` is UCT by
   two-out-of-three.  The image `S` of `ι_P^{-1}(G_0)` satisfies `σ̄^(S) = 0` and
   contains `∂(K_1(A/I_P))`.
2. The unital corner with faithful trace `t` embeds unitally in a `Q`-stable AF
   algebra realising `x ↦ t^(x)` (Moutzouris Theorem 4.1).  Stabilising gives
   `θ : I_P/N -> D_0` injective with `θ_*(S) = 0` in `K_0(D_0)`.  `D_0` is full
   hereditary in an ideal of the separable AF algebra `B ⊗ K`, and that ideal's
   `K_0` injects into `K_0(B ⊗ K)`.
3. `A/N` embeds in the separable extension `A''` of `A/I_P` by `D_0` generated
   by `(θ̃μ(a), π(a))` and `D_0`.  It has zero boundary, so it is
   quasidiagonal (Brown–Dadarlat Theorem 3.4).  It kills `G_0`.
4. Positivity at `Q_{i,ε} ∈ her((a_i - 2ε)_+)` puts `Q_{i,ε}` in `ideal(a)`
   outside each kernel, so the kernels intersect in `0`.
5. `separating-killing-quotients-give-faithful-qd-killing` glues the maps.
