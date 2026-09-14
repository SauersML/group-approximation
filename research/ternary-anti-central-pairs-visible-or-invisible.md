---
rg: 2
id: ternary-anti-central-pairs-visible-or-invisible
kind: claim
title: One-sided pairs on the ternary anti-central summand normalize to lifts of (s0, t0) or to pairs over the unit, and corner solutions are always visible
distinct_from:
  leavitt-inverse-defects-are-visible-or-invisible: that is the binary normalization in F_2[R^x], where the augmentation forbids a defect equivalent to 1; this is the anti-central summand over F_3, which has no augmentation, and where the Kaplansky trace does that job and the corner equation is forced visible.
  ternary-twisted-algebra-has-swap-separated-one-sided-pair: that is an exact reformulation of the corner equation as a swap-separated pair; this normalizes every one-sided pair of the summand and proves every corner or swap-separated solution evaluates to an honest pair.
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

Let `S_- = eps_- F_3[G]`, `G = L_(F_3)(1,2)^x`, `pi : S_- -> R` the evaluation,
`K_- = ker pi`, and let `c a = eps_- != a c` in `S_-`, with defect `delta = eps_- - ac`.

* **(V3)** If `pi(delta) != 0`, one group translate gives `pi(a) = s0` and `pi(c) = t0`. The
  orbit theorem for `L_k(1,2)` holds over every field; only Lemma 1 changes, by dividing out a
  nonzero leading coefficient.
* **(I3)** If `pi(delta) = 0`, one translate gives `pi(a) = pi(c) = 1` and a defect in `K_-`.

Hence `S_-` fails direct finiteness iff some lift of `s0` is left invertible (with partner over
`t0`) or `F_3 eps_- + K_-` is not directly finite.

**Visibility.** If `ac` lies under an idempotent `p` with `pi(p) != 1`, then
`pi(a)pi(c) != 1`. So every solution of `ternary-anti-invariant-swap-corner-is-full`, and every
swap-separated pair, is visible. The kernel cannot supply a corner solution by itself.

**Trace.** `S_-` has no augmentation, but `tau(delta) = 0 != 2 = tau(eps_-)`. So no defect is
equivalent to `eps_-`, and no defect is a single Klein kernel idempotent.

**Unit criterion.** (V3*) holds iff some lifts `alpha0` of `s0` and `beta0` of `t0` have
`beta0 alpha0` a unit of `S_-`. By `ternary-anti-central-kernel-has-klein-idempotents`,
`eps_- + K_-` contains non-units, so this is a genuine condition.

Proof: Sections 2 and 3 of the artifact.
