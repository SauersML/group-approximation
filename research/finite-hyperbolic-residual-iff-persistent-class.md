---
rg: 2
id: finite-hyperbolic-residual-iff-persistent-class
kind: claim
title: Finite nontrivial hyperbolic residuals exist exactly when persistent prime central classes do
distinct_from:
  persistent-degree-two-class-on-hyperbolic-group: that is the open existence assertion; this proves equivalence with three algebraic existence formulations without deciding any of them.
  finite-kernel-nonrf-has-central-prime-reduction: that constructs a prime central extension from a supplied arbitrary finite-kernel extension of an RF base; this specializes to hyperbolic groups and characterizes the exact scope of the persistent-class route.
  universal-hyperbolic-vtf-iff-rf: that compares universal residual finiteness and virtual torsion-freeness; this concerns counterexamples with finite nontrivial residual and does not cover an arbitrary infinite residual.
artifacts:
  - notes/HYPERBOLIC_FINITE_RESIDUAL_REDUCTION_2026-09-07.md
---

The following existence statements are equivalent:

1. A word-hyperbolic group `G` has `1<|R(G)|<infinity`.
2. A residually finite word-hyperbolic group has a finite-kernel extension
   which is not residually finite.
3. A residually finite word-hyperbolic group has a central extension by
   `C_p`, for some prime `p`, whose finite residual is exactly `C_p`.
4. A residually finite word-hyperbolic group `H` has a class in
   `H^2(H;C_p)`, with trivial coefficient action, whose restriction to
   every finite-index subgroup is nonzero.

This claim establishes the equivalence only. All four existence
assertions remain open. In particular it neither establishes nor refutes
[[persistent-degree-two-class-on-hyperbolic-group]]. The complete proof
is Section 4 of the artifact, using the central-prime reduction of
Section 3. These are standard elementary deductions, with no historical
novelty or Lean-verification claim.

The finite residual is the intersection of finite-quotient kernels,
not the maximal finite normal subgroup. A hyperbolic counterexample
with infinite residual is not reduced to one of these forms by this
argument.
