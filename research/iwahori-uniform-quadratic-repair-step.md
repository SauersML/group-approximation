---
rg: 2
id: iwahori-uniform-quadratic-repair-step
kind: claim
title: The Iwahori mismatch admits a uniform three-halves repair step with summable padding
distinct_from:
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: that repairs pairs already factoring through odd congruence quotients, in one linear step and with no padding budget; this asks for one step of rate three halves at arbitrary pairs, and only for a step, not for the whole modulus.
  iwahori-local-global-defect-question: that is the modulus itself, the published question; this is a quantitative single-step statement that implies it through the completion budget and is strictly stronger.
  iwahori-admits-neutral-quadratic-directions: that asks only for the neutral direction with its projected quadratic effect; this is the resulting step, including the defect rate, the movement and the padding bound.
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

**OPEN.**  Let `C` be the class of pairs of finite-dimensional unitary
representations of the two modular vertex groups, with `def` as in
`iwahori-local-global-defect-question`.  Ask for constants `A, B` and a
threshold `eps > 0` such that every `pi` in `C` of dimension `d` with
`def(pi) <= eps` admits `pi^+` in `C` of dimension `d + r` with

```text
def(pi^+) <= A def(pi)^(3/2),
max_s d_0( pi^+_s, pi_s ) <= B sqrt(def(pi)),
r <= B def(pi) d,                                                       (QS1)
```

the constants being the same at `pi^+` as at `pi`, so that the step may be
applied to its own output.

By `quadratic-repair-steps-complete-in-finite-dimension` this answers
`iwahori-local-global-defect-question` positively with the square-root modulus,
and hence, through `iwahori-sector-closure`, produces a non-hyperlinear finite
central extension of `SL_2(Z[1/2])`.

## Attempts

- **Through the second-order mechanism.**  The route
  `iwahori-quadratic-step-from-neutral-directions` derives `(QS1)` from
  `iwahori-admits-neutral-quadratic-directions` and
  `second-order-step-beats-a-blocked-linearization`.  The whole difficulty is
  the first prerequisite; see its own attempts, in particular that the
  directions cannot come from the compatible locus.
- **Through the linear theory, in the near sector only.**  `(UIR)` plus an
  operator-norm proximity hypothesis gives a linear step there, by the true
  statement recorded at the end of
  `normalized-hs-taylor-remainder-is-not-dimension-free`.  That statement is in
  the wrong metric for this question, which is posed in normalized HS, so it
  does not supply `(QS1)`.
- **Closure under the step's own output is the load-bearing clause.**  A
  one-stage estimate is not enough: the audit at
  `research/artifacts/parallel-ui-iteration-audit-2026-09-04.md` records
  exactly this failure mode, where each stage is uniform and the iteration is
  still unjustified.  Any candidate proof must show its hypotheses hold at the
  repaired pair with the same constants, which is where padding by inexact
  blocks is dangerous: it can move the new pair into a stratum the hypothesis
  does not cover.
- **The rate is not negotiable downward.**  A step with only a constant-factor
  gain cannot be iterated to exactness; the accounting is the same as in
  `quadratic-descent-loss-is-admissible-linear-is-not`, and the three-halves
  rate is what makes the defects geometric and the padding summable.
