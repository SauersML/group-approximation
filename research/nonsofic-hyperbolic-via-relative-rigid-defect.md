---
rg: 2
id: nonsofic-hyperbolic-via-relative-rigid-defect
kind: route
title: Contrapose the relative defect criterion against the hyperbolic Kazhdan cover of the Leavitt unit group
target: nonsofic-hyperbolic-group
requires:
  - sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels
  - hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

`hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup` gives:

- a word-hyperbolic Kazhdan group `G`;
- a normal Kazhdan subgroup `N`;
- a rigid pair `N <= Gamma_hat <= G_hat <= G`, and `z`, `u_hat`, `gamma` with
  `[z, Gamma_hat] <= N` and `[u_hat z u_hat^-1, gamma] not in N`.

If `G` were sofic, the relative criterion with `H = G` and `M = N` would put
that commutator in `N`. So `G` is not sofic. It is word-hyperbolic and Kazhdan,
and it is not residually finite.

**Why this route is new.** `nonsofic-hyperbolic-via-kun-thom-centralizer` and
the compression transplants died because absolute defects vanish in
hyperbolic groups. This route asks the sofic criterion to see a defect only
modulo a Kazhdan kernel, and there the hyperbolic category has an explicit
counterexample configuration. All the difficulty sits in the premise.
