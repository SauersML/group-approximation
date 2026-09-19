---
rg: 2
id: definetti-group-table-rounding
kind: claim
title: Dimension-free symmetric-extension rounding of a finite multiplication table
distinct_from:
  hyperlinear-implies-sofic: that is the group statement, quantified over all groups and all windows at once; this is a single quantitative theorem about one finite table, with its own extension level and defect threshold chosen in a fixed order.
  group-table-cpsd-cp-face-collapse: that asks for equality of convex closures on a special face; this asks for a quantitative finite-level rounding theorem.
  geometric-schreier-design: that rounds a mean-square spherical almost action by geometric matching; this rounds a symmetric-extension moment object whose hard issue is assignment-side integrality.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

**Corrected target.** For every finite partial multiplication table `T` and
`eps>0`, construct an **assignment/context-side** symmetric-extension
relaxation `Q_m(T)` and choose `m=m(T,eps)` and `eta>0`, independent of the
matrix dimension, such that every regular-trace unitary table of defect
`<eta` lifts to `Q_m(T)` and the lifted point rounds to a multiplicative Markov
model (or directly to permutations) with error `<eps`.

The word **assignment/context-side** is load-bearing. The second proof sprint
killed the naive interpretation in which one simply takes independent balanced
copies of a character coefficient and applies de Finetti across those copies:
`replica-definetti-saturation-no-go` proves that state is already product
across the replica split. A useful symmetric extension must live over internal
path/assignment variables that still remember multiplication.

A viable encoding still needs four properties:

- **DF1, unitary lift.** A microstate of defect `delta`, after whatever balanced
  amplification the encoding uses, gives a feasible symmetric point with
  controlled violation and no matrix-dimension factor.
- **DF2, dimension-free local norm.** The table observables are controlled in
  normalized HS norm with constants depending on `T,m`, not on `d`.
- **DF3, genuine classicalization.** The de Finetti/argmax conclusion destroys
  nonclassical correlation in the assignment split, not merely between copies.
- **DF4, multiplicative endpoint.** The rounded object gives one common latent
  Markov/permutation table preserving products, inverses and regular trace.
  By `markov-sofic-equals-sofic`, it is enough to reach doubly stochastic
  kernels; final permutation integrality is no longer the hard part.

`balanced-replica-hs-amplification` remains useful parameter arithmetic: one
may choose a replica/extension scale after fixing `T` and then request a
microstate accurate enough that the amplified HS defect is tiny. What it no
longer supplies by itself is DF3.

The 2026 dimension-free HS de Finetti results of Jeronimo--Wu--Xu and Miyamoto
remain relevant inspiration, but they do not automatically apply to this
custom group-table split. The exact Bose-marginal calculation is preserved in
the integration artifact, and `covariant-separable-relative-signal-ceiling`
shows that any covariant separable two-register endpoint retains at most
`1/(d+1)` of the relative coherent trace. A successful theorem must therefore
exploit higher-order/whole-table structure.

## Attempts

- **Independent balanced replicas.** Explicitly dead:
  `definetti-via-independent-balanced-replicas`, invalidated by
  `replica-definetti-saturation-no-go`.
- **Canonical covariant two-register Bose moments.** Dead as a direct
  dimension-free endpoint: `definetti-via-covariant-second-moments`, invalidated
  by `covariant-separable-relative-signal-ceiling`.
- **Dephase first and then impose relations.** Dead:
  `dephasing-destroys-multiplicativity`.
- **Replicate arbitrary channels and invoke quantum Birkhoff.** Dead:
  `asymptotic-quantum-birkhoff-false`.
- **Entrywise tropical/argmax selection.** Fourier-type blocks have large ties;
  generic tie breaking destroys multiplicative coherence.
- **Surviving test case.** The associativity square
  `gh=k`, `hr=s`, `gs=t`, `kr=t` is the smallest whole-table instance on which
  an assignment-side symmetric extension can be stress-tested. If no
  dimension-free collapse occurs there, this route should be abandoned.
