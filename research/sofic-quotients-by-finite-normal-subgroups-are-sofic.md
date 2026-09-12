---
rg: 2
id: sofic-quotients-by-finite-normal-subgroups-are-sofic
kind: claim
title: The quotient of a sofic group by a finite normal subgroup is sofic
distinct_from:
  sofic-quotients-by-kazhdan-normal-subgroups-are-sofic: that is the open case of an infinite Kazhdan kernel, where one expander block of the kernel is not covered by boundedly many kernel elements; this is the finite-kernel case, where every kernel orbit has exactly |M| points and freeness passes to the orbit set.
  amenable-quotient-preserves-metric-approximability: that passes soficity up from a kernel along an amenable quotient; this passes soficity down from a group to its quotient by a finite kernel.
---

**ESTABLISHED.** Let `H` be a countable sofic group and `M` a finite normal
subgroup of `H`. Then `H/M` is sofic.

Derivation: `sofic-quotients-by-finite-normal-subgroups-are-sofic-proof`. The
argument is elementary. No published source was checked for it, so it is not
claimed as new.

## Consequence for the relative defect criterion

Finite groups have property (T), so finite `M` is admissible in
`sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`, and for such `M` that
criterion holds.

- `H/M` is sofic.
- A rigid pair `Gamma <= G <= H` with `M <= Gamma` maps to a rigid pair
  `Gamma/M <= G/M` of `H/M`: images of Kazhdan groups are Kazhdan, and the
  compressor semigroup still generates.
- `[z, Gamma] <= M` means `zM` centralizes `Gamma/M`. The absolute criterion
  `sofic-groups-kill-rigid-compression-defects` in `H/M` puts
  `[g z g^-1, gamma]` in `M`.

So a counterexample to the relative criterion needs an infinite Kazhdan kernel.
