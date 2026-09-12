---
rg: 2
id: jnvwy-no-safe-alternative-introspection-proof
kind: route
title: Combine the ComputeSampler nonlinear triple with exact full-seed rigidity
target: jnvwy-introspection-has-no-affine-safe-perfect-model
requires:
  - jnvwy-compute-sampler-has-nonlinear-role-marginal
  - jnvwy-perfect-introspection-forces-full-seed-support
---

The first required claim proves directly from the fixed sampler, independently of strategy and PCP witness choices, that a
role marginal `L` of the unchanged recursive `ComputeSampler(lambda)` has
seeds `z_0,z_1,z_2` satisfying

```text
L(z_0)+L(z_1)+L(z_2) != L(z_0+z_1+z_2).
```

The second required claim proves from the exact Pauli, Pair, Magic-Square, and
sampling equations that every perfect model of the corresponding
introspection verifier contains positive Intro--Sample atoms above all three
seeds, and that their odd xor is rejected.  Hence no perfect model at this
stage has affine-safe support on every sampled edge.
