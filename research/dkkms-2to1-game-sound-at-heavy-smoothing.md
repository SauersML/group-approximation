---
rg: 2
id: dkkms-2to1-game-sound-at-heavy-smoothing
kind: claim
title: For every delta > 0 there are l >= 3, a fixed smoothing rate beta in (0,1), s in (1/2, 1) and k_1 such that for every k >= k_1 the folded DKKMS 2-to-1 reduction at (l, k, beta) sends every 3LIN instance of value <= s to a game of value <= delta
distinct_from:
  two-to-two-games-theorem: that is soundness at the DKKMS rate beta = log log k / k, where the class seed law is flat; this asks for soundness at a fixed rate, where the class seed law concentrates, which the published proof does not reach.
  dkkms-grassmann-2to1-test-is-locally-99-percent-rigid: that is a rigidity target on the admissible range of the paper's rate; this is a soundness statement at a different smoothing rate, with no rigidity form asked for.
  efficient-branch-selector-on-proved-2to1-instances: that asks for a near-perfect selector where soundness is proved; at fixed beta the selector is already supplied by dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games, and this asks for the soundness instead.
  rich-2to1-perfect-completeness-conjecture: that asks for rich 2-to-1 hardness with perfect completeness on some instance family; this is plain 2-to-1 soundness for one explicit family, with completeness supplied by the construction.
---

**OPEN.** The notation is that of
`dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games`. `G(I; l,k,beta)` is
the folded DKKMS game (TR16-198 §4.2) built on a regular 3LIN instance `I`,
with smoothing rate `beta`.

## Statement

```text
for every delta > 0 there are l >= 3, beta in (0,1), s in (1/2, 1) and k_1 such that
for every k >= k_1:  val(I) <= s  implies  val(G(I; l,k,beta)) <= delta.
```

## Why it is the last hole

By `ugc-from-dkkms-soundness-at-heavy-smoothing`, this statement together with
the ESTABLISHED free-bit node implies `unique-games-conjecture`.

- **Completeness.** At a fixed `beta`, completeness is handled by
  Theorem H: `xi -> 0` as `k` grows.
- **Soundness of the lift.** This is free by Theorem F(2).
- **Only this statement is left.** No hypothesis about selectors, rigidity or
  folding-compatibility remains.

## What is known and where proofs stop

- **The outer game improves with beta.** The smoothed projection game at a fixed
  `beta` is the `k`-fold repetition of a base game. That base game tests an
  equation against one of its variables with probability `beta`. So
  parallel repetition drives its value down like `exp(-Omega_beta(k))`. The
  paper's rate gives only `exp(-Omega(log log k))`.
- **The published inner analysis needs small beta.** The smooth-advice step
  (DKKMS Lemmas 4.10 and 5.3, quoted in
  `dkkms-certified-parameters-lie-in-the-selector-kill-regime`) forces
  `beta sqrt(k) 2^l << 1`. That is exactly the flat side of Corollary D.
- **The covering transfer cannot reach fixed beta.** The transfer of
  `dkkms-seed-law-is-uniform-in-regime-and-far-in-window` (Theorem W) is dead
  there: the seed law is far from every transitive law.
- **The concentration gives no NO labelling by itself (heuristic).** At fixed
  `beta` an A-vertex puts mass `1 - exp(-Omega(k))` on its generating seed.
  Copying the dominant B-neighbour's label would then satisfy almost every
  edge, if folding allowed it. Folding forces the class label to agree with
  `h_U` on `H_U`. Different members of a class have seeds that differ by
  `H_U`-vectors, so class consistency of the B-labels is a test of the
  equations `h_U`. What is left is the question of whether this
  class-consistency test on B-labels is sound. That reformulation is a
  heuristic and is not proved here.
- **Not via outer-honest rigidity (unchecked).** At fixed `beta` the free bit
  is a polynomial-time selector with near-perfect YES lifts. If the argument of
  `near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp` applied at
  these points, it would give `NP in RP`. So a proof through Theorem R's
  conclusion is not expected.

## How it can fail

A NO labelling family with value bounded away from `0` at every fixed `beta`
refutes the statement. So does a proof that the class-consistency test accepts
non-codeword B-labellings with constant probability. Either would also close
off the free-bit route to UGC.

## Attempts

- **2026-09-17, swarm-0917-w16-w16-ugc-last1: import the published soundness
  proof.** This dies at the smooth-advice step.
  - DKKMS Lemmas 4.10 and 5.3 need `sqrt(beta) k^(1/4)`-type smallness, and
    `beta sqrt(k) 2^l << 1` fails at every fixed `beta` once `k` is large.
  - The covering-lemma transfer to a transitive Grassmann test also dies
    there. The axis-projection event of Theorem W in
    `dkkms-seed-law-is-uniform-in-regime-and-far-in-window` has probability
    `1 - exp(-Omega(beta k))` at a fixed `beta`, so the seed law is at total
    variation near `1` from every transitive law.
  - No proof is known that avoids both steps. The class-consistency
    reformulation above is the proposed next attack, and it is deferred.
