---
rg: 2
id: v-nilpotent-abelian-from-hyperbolic-points
kind: route
title: A central commutator with a hyperbolic fixed point has slope zero there, a contradiction
target: torsion-free-nilpotent-subgroups-of-thompson-v-are-abelian
requires:
  - infinite-order-elements-of-v-have-hyperbolic-periodic-points
artifacts:
  - research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part3.md
---

Full derivation in the artifact: Lemma V-A (proved there) and §N1-V. Summary:

- Take `z = [x,y] ≠ 1` central in a torsion-free class-2 subgroup. By the required claim,
  some `z^k` has a hyperbolic fixed point.
- Its hyperbolic fixed points form a finite set `P`, which `x` and `y` permute. So
  `x^r`, `y^r` and `z^r` fix `P` for `r = |P|!`.
- The slope homomorphism at `p` in `P` kills `[x^r, y^r] = z^{r^2}`, but `z^k` has
  nonzero slope there.
