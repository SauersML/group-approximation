---
rg: 2
id: cyclic-input-window-zero-needs-an-automorphism-twist
kind: claim
title: For the input Z, a genuine shell action passes window zero only with an automorphism twist; the endomorphisms a ↦ a^k with |k| ≥ 2 are impossible in both directions
distinct_from:
  fw-inputs-pass-window-zero-only-via-proper-self-embeddings: that leaves open, for FW inputs, window zero of sign −1 through an injective endomorphism of infinite index; this shows that for the simplest non-FW input, Z, no non-surjective endomorphism twist works in either direction, so endomorphism twists are not an easy source of window-zero witnesses.
  eventually-periodic-genuine-shell-actions-give-fp-envelopes: that constructs window-zero actions of virtually abelian inputs through finite-order automorphism twists; this shows that for Z those are the only twists, since the other injective endomorphisms a ↦ a^k are excluded.
  fw-window-zero-descending-sign-forces-trivial-core: that excludes co-Hopfian FW inputs; Z is not FW and not co-Hopfian, and this excludes its non-surjective twists by a different counting argument along the shift ray.
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

**ESTABLISHED** by `cyclic-input-window-zero-needs-an-automorphism-twist-proof` (lane proof, elementary, not independently reviewed, no priority claimed).

## Setting

`P = Z = <a>`. `alpha ∈ Sym(N)` is a permutation such that `alpha^n` moves infinitely many points for every `n != 0`; this is the infinite-support hypothesis of `genuine-action-shell-envelopes-generalize-the-regular-shell` for `rho(a) = alpha`. `s: n ↦ n+1`. Every injective endomorphism of `Z` is `a ↦ a^k` with `k != 0`. The automorphisms are `k = ±1`.

## Statement

For every integer `k` with `|k| >= 2`, neither of the following holds near infinity:

- (−) `s alpha s^-1 = alpha^k` (window zero, sign `−1`, twist `a ↦ a^k`);
- (+) `s^-1 alpha s = alpha^k` (window zero, sign `+1`, twist `a ↦ a^k`).

Consequently, a genuine action of `Z` with infinite supports passes the window-zero gate only with an automorphism twist `a ↦ a^(±1)`. By item 5 of `eventually-periodic-genuine-shell-actions-give-fp-envelopes`, such an action is eventually periodic.

## The mechanism

The shift is a single ray through `N`. Near-equivariance forces some quantity attached to a point to move monotonically along that ray, while each value of the quantity is taken by infinitely many points. A single ray cannot visit all of them.
- On the lines (infinite orbits) of `alpha`, the quantity is the line coordinate, which `s` multiplies by `k`, up to bounded error.
- On the cycles, it is the cycle length. Cycles of each length form finite blocks that the ray cannot leave infinitely often.

Two finer points:
- The count of ends (two per line) forces infinitely many lines as soon as there is one.
- Only finitely many defects are allowed, so all but finitely many points obey the exact affine rule.

## Scope

- Only `P = Z` is treated. A virtually cyclic input with a finite normal subgroup, or a two-generator input, is not covered.
- For FW inputs the corresponding sign-−1 case, a proper self-embedding of infinite index, stays OPEN. The counting used here needs finite orbits or two-ended orbits with coordinates, and the FW residual case has neither: its orbits are highly transitive.
- The statement gives no finite-presentation information.
