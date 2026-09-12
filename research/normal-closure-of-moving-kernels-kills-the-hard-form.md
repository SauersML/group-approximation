---
rg: 2
id: normal-closure-of-moving-kernels-kills-the-hard-form
kind: claim
title: Imposing the moving kernels in one normal module destroys the Boolean hard form
artifacts:
  - experiments/paired_frame_moving_kernel_orbit.py
distinct_from:
  paired-frame-moving-kernel-is-a-rank-one-veronese-clock: that proves the kernels differ by one moving line at each pair of levels; this computes their cumulative relation span and the surviving dual form after all conjugate relations are imposed.
  paired-hard-form-transverse-to-moving-clock: that proves the hard form detects every moved line; this draws the group-presentation consequence that those lines cannot all be relations in one normal coefficient module.
  one-sided-paired-frame-reverse-reservoir-collapse: that permits partial corner or site placements; this rules out only a global linear normal-module realization of all levels.
---

Let `W` be the `F_2(x)`-span of all transported relation kernels from
`(MVK1)`.  Then

```text
dim W=5,
W=span{e_01,e_23,e_02,e_03+e_12,e_13}.                 (NCM1)
```

Therefore its annihilator in the alternating-form dual is the single line

```text
W^perp=span{e_03^*+e_12^*}.                            (NCM2)
```

The Boolean hard form `h=e_02^*` is not in `(NCM2)`; already
`h(v_1)=x^2!=0`.

Consequently, suppose one tries to realize the clock in a single class-two
normal `F_2[x]`-module on four noncentral generators, imposes the relations
`K_0`, and lets a stable group word conjugate the generators by `T`.  Normal
closure automatically imposes every conjugate relation `K_n`, hence all of
`W`.  Every surviving commutator form must annihilate `W`, so the hard form is
forbidden and the Boolean rank jump disappears.

Thus the favorable pairwise rank-one motion cannot be globalized by an
ordinary semidirect product or linear ascending HNN module.  A successful
transducer must keep levels in genuinely different spectral corners or sites,
or impose the kernels only after compression by level projections.  This is
the precise sense in which a moving-kernel **atlas**, rather than a moving
normal subgroup, is required.
