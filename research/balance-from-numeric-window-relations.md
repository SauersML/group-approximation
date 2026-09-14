---
rg: 2
id: balance-from-numeric-window-relations
kind: route
title: Remove the boundary factor from window counts with translation totals, the decoder bound and a Garden of Eden
target: every-injective-ca-preserves-uniform-bernoulli-measure
requires:
  - window-balance-is-a-fiber-upper-bound
  - decoder-window-fiber-bound-loses-exactly-the-boundary
artifacts:
  - research/artifacts/window-balance-mass-transport-2026-09-12.md
  - research/artifacts/numeric-window-relations-no-go-2026-09-12.md
---

**Dead.** It is invalidated by `numeric-window-relations-do-not-force-balance`.

**The idea.**
- Balance is the fiber upper bound `c_E(p) <= q^(|EM| - |E|)` on a cofinal family of windows
  (`window-balance-is-a-fiber-upper-bound`).
- Injectivity gives that bound up to the factor `q^|d_N E|`
  (`decoder-window-fiber-bound-loses-exactly-the-boundary`).
- The route removes the factor by combining the bound with translation invariance and totals, integrality
  and dependence range of the counts, and the zero at a Garden of Eden. The combining could be mass
  transport of counts along the decoder graph, averaging over translates or invariant random windows, or
  telescoping `tau`, `sigma`, `tau` at the level of counts.

The same approach can instead use the image's uniform Gibbs specification and completion counts
(`research/artifacts/gottschalk-injective-image-uniform-gibbs-bridge-2026-09-08.md`).

**Why it dies.** Every such manipulation uses the counts only as numbers, satisfying the relations of the
invalidating claim. Unbalanced measures satisfy those relations in three cases:
- iid merge measures satisfy R1–R4 at every alphabet size `q` with `q^(1 - theta_N) >= 2`, over every
  nonamenable decoder memory group;
- AND measures satisfy R1–R4 at `q = 2` whenever the decoder memory contains a free radius-2 ball;
- projection measures satisfy R1–R4 and every relation of the Gibbs bridge at every `q = r^k` with
  `k >= 1/(1 - theta)`.
