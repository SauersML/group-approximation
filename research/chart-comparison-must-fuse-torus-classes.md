---
rg: 2
id: chart-comparison-must-fuse-torus-classes
kind: claim
title: Every finite image of a half-corner comparison's actor group must fuse the three order-three torus classes of GL_2(F_4)
invalidates: [half-corner-comparison-via-finite-actor-images]
distinct_from:
  split-comparisons-balance-induced-brauer-characters: that is the general balance theorem for any finite chart and any pair of equal-rank projectives; this computes the Brauer difference of the specific half-corner projectives and reads off the three torus classes it forces to fuse.
  half-corner-chart-comparison-exists: that is the open existence question for the comparison itself; this is an established necessary condition on the actor group of any solution, which does not decide existence.
artifacts:
  - research/artifacts/kaplansky-torus-fusion-brauer-balance-2026-09-11.md
  - research/artifacts/kaplansky-half-corner-feedback-and-projective-defects-2026-09-08.md
  - research/artifacts/gottschalk-negative-side-verification-2026-09-12.md
---

Let `Q = L_(F_2)(1,2)^x`, `S = F_2[Q]`, and let `K = GL_2(F_4)` be the half-corner
chart on the leaves `(000,001 | 010,011)`, with its projectors `f_+, P` (rank
40) and `f_0, P_0` (rank 32). Put

```text
T0 = class of diag(G, G^2),   T1 = class of diag(G^2, I_2),   T2 = class of diag(I_2, G),
```

the three `K`-classes of elements `a z^k` with `a in SL_2(F_4)` of order three.

**Claim.** Suppose `Z in P_0 S f_0` and `L in f_0 S P_0` satisfy `L Z = f_0`, or
the same for `(f_+, P)`. Let `H <= Q` contain `K` and the support of `Z`. Then for
every homomorphism `pi : H -> F` to a finite group which is injective on `K`,
the classes `pi(T0), pi(T1), pi(T2)` coincide in `F`.

The source is the Brauer difference of the two projectives. By the half-corner
module identification, `f_0 ~ P(1)+St` and `P_0 ~ P(V)+P(V^(2))` over `F_4[A_5]`.
Their difference, weighted by centralizer orders, is `+2/3` on `T0`, `-1/3` on
`T1` and on `T2`, and zero elsewhere. It balances in a finite image only after
all three classes fuse.

Consequences.

* Every actor family with a finite coordinate interpretation, in which `K`
  acts through natural `F_4`-blocks plus trivial coordinates, is excluded at
  every coefficient choice and every support. Fixed-space dimensions separate
  `T0` from `T1, T2` there. This uniformly recovers the recorded
  finite-specialization exclusions (half-corner Sections 10, 11, 12 and 14).
* `Q` itself fuses the three classes by prefix permutations. So every lifted
  Hattori--Stallings rank, and every additive invariant of `K_0(S)`, agrees on
  `f_0` and `P_0`. Only finite-image or module-level arguments can obstruct the
  comparison.
* A live comparison must use actors whose every chart-injective finite image
  fuses `T0 ~ T1 ~ T2`. In `Q` this fusion is carried by depth-changing prefix
  permutations.

ESTABLISHED by [[torus-fusion-from-brauer-balance-proof]].
