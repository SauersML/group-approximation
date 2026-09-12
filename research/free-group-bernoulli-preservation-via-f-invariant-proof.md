---
rg: 2
id: free-group-bernoulli-preservation-via-f-invariant-proof
kind: route
title: Transport entropy along the Cayley tree with the f-invariant and submodularity on balls
target: free-group-injective-ca-preserve-bernoulli-via-f-invariant
requires:
  - bowen-f-invariant-is-a-measure-conjugacy-invariant
  - injective-measure-preserving-ca-is-surjective
artifacts:
  - research/artifacts/free-group-f-invariant-bernoulli-preservation-2026-09-12.md
---

Complete proof, Sections 2 to 4 of the artifact.

* **Splitting monotonicity** (Lemma 2.1, elementary). `F(beta v t gamma) <= F(beta)`
  for `t = s_j^(±1)` and `gamma <= beta`, by submodularity. The ball refinement
  `eta^(B_(n+1))` is reached from `eta^(B_n)` by `2r` such splittings with
  `gamma = eta^(B_n)`, so `f = inf_n F(eta^(B_n))`.
* **Invariance** (the prerequisite). The injective automaton is a measure conjugacy
  onto its image, and the coordinate partitions are generating. So
  `f(tau_* mu) = f(mu) = log q`.
* **Induction.** `B_n ∩ s_i B_n = B_(n-1) ∪ s_i B_(n-1)` and
  `|B_n| - sum_i |B_n ∩ s_i B_n| = 1`. Together with the bound
  `F(eta^(B_n)) <= H(B_n) - sum_i H(B_n ∩ s_i B_n)`, they force uniform laws
  alternately on `B_n` and on `B_n ∪ s_i B_n`.

Surjectivity then follows from `injective-measure-preserving-ca-is-surjective`.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 4.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). Lemma 2.1 is needed in the general form `F(beta v t gamma) <= F(beta)` with `t = s_j^(±1)` and `gamma <= beta`, because the ball refinements are reached by those splittings, not by `alpha -> alpha v s alpha`; the same submodularity count proves it.
