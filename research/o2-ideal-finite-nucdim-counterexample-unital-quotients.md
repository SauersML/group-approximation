---
rg: 2
id: o2-ideal-finite-nucdim-counterexample-unital-quotients
kind: claim
title: A separable O_2-multiplier ideal of finite nuclear dimension with non-K1-injective unitization can be taken with unital quotients on every nonzero ideal
distinct_from:
  o2-multiplier-ideal-with-non-k1-injective-unitization: that is the open existence claim; this is an established constraint on its finite-nuclear-dimension witnesses.
artifacts:
  - research/artifacts/k1-o2-ideal-finite-nuclear-dimension-2026-09-13.md
---

Let `I` be non-unital, with a unital copy of `O_2` in `M(I)`, and `A = C*(I, O_2)`.

1. `I` has no nonzero bounded trace.
2. If `I` is stable, then `Ĩ` is K1-injective.
3. Suppose `I` is σ-unital with nuclear dimension at most ω, and `Ĩ` is not K1-injective. Then `I` has a
   nonzero unital quotient `Q = I/K`, `Q` contains `O_2` unitally, and `A/K ≅ Q ⊕ O_2`.
4. Suppose `I` is separable with nuclear dimension at most ω, and `J_0` is the largest ideal of `I` with no
   nonzero unital quotient. Then `J_0` is stable, and if `Ĩ` is not K1-injective, neither is `(I/J_0)~`.
   Every nonzero ideal of `I/J_0` has a nonzero unital quotient.

The pointer "σ-unital, finite nuclear dimension, no bounded traces implies stable" is false as recalled:
`C_0([0,1)) ⊗ O_2` fails it. The correct theorem, Robert arXiv:1002.2180v2 Corollary 1, also requires no
nonzero unital quotients. Item 3 is the version that applies to counterexample ideals. So a counterexample
ideal need not have infinite nuclear dimension. If its nuclear dimension is finite, it must carry unital
quotients, and each of them contains `O_2` unitally.
