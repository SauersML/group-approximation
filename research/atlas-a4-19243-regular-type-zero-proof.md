---
rg: 2
id: atlas-a4-19243-regular-type-zero-proof
kind: route
title: Fiber the regular A4 restriction flow with the balanced regular-S3 collision family
target: atlas-a4-19243-type-relaxation-has-regular-zero
requires:
  - atlas-a4-context-types-live-in-fixed-rational-polytope
  - atlas-a4-context-type-vector-converges-to-regular-point
  - atlas-19243-has-continuous-regular-s3-line-holonomy
---

For a finite group `G` and subgroup `H`,

```text
Res_H^G Reg(G)=[G:H] Reg(H).                           (ATP5)
```

The multiplicity of `pi in Irr(H)` in the right side is
`[G:H]dim(pi)`.  Dividing by `|G|` gives `dim(pi)/|H|`, which proves every
restriction equation in `(ATP1)` for `(ATP2)`.  The dimension equations are
the character identity `sum_pi dim(pi)^2=|H|`.  The displayed A4, C2, C3,
and S3 coordinates follow immediately.

The established context-type convergence theorem shows that this is exactly
the leading profile relevant to a canonical atlas microstate sequence, not an
extraneous face of `P_A4`.

For collision, use the established six-dimensional representation

```text
(triv directSum sign) directSum std_+ directSum std_-.
```

Its `S3` multiplicities are `(1,1,2)`, giving `(ATP4)`, and the construction
has three positive and three negative eigenvalues for `c`.  It satisfies the
collision word exactly for every reflection angle.  Since
`20160/6=3360`, its `3360`-fold amplification has exactly the regular-A8
restriction dimension and balanced transvection spectrum.  This supplies the
collision side of the type fiber product and proves the intersection.

Because every coordinate is rational, this is an exact feasible point, not
only a limiting real profile.  The final qualification follows because
restriction multiplicities and spectral ranks contain no relative
intertwiner or common-frame coordinate.
