---
rg: 2
id: stw93-same-slice-si-does-not-force-central-capacity
kind: claim
title: Same-slice property (SI) does not force infinite capacity outside the slice
distinct_from:
  stw93-saturated-slice-data-allow-residual-trace: that theorem shows the established saturated slice and quotient data permit a residual trace; this theorem identifies the sharper finite-Cuntz-capacity failure and verifies same-slice property (SI) in the same model.
  stw93-mixed-z-slice-si-forces-infinite-capacity: that positive reduction assumes arbitrary trace-kernel sources; this no-go proves that replacing them by sources in the Jiang--Su slice loses exactly the needed conclusion.
  stw93-faithful-full-diagonal-retains-norm-kernel: that faithful MF model produces only infinite-capacity kernel projections; this abstract doubled-slice model produces a kernel projection of capacity exactly one but is not asserted to be an actual central sequence algebra.
artifacts:
  - research/artifacts/stw93-mixed-slice-capacity-audit-2026-08-30.md
---

There is a pure unital C*-algebra `D_0` with trace-kernel ideal `I_0`, a
unital diagonal slice `delta:F(Z)->D_0`, and a projection `p in (I_0)_+`
such that:

1. `D_0/I_0` is the hyperfinite II_1 central-sequence factor;
2. the diagonal slice exhausts `D_0/I_0`;
3. every property-(SI) test pair whose source and target both lie in the
   diagonal slice has its witness in that slice; but
4. `cap_(D_0)(p)=1`.

Indeed one may take

```text
G=F(Z),        D_0=G direct_sum G,
I_0=J_(tau_G) direct_sum G,       delta(x)=(x,x),
p=(0,1_G).
```

Every nonzero spectral cut `(p-epsilon)_+`, `0<epsilon<1`, is Cuntz
equivalent to `p` and also has capacity one.  Therefore same-slice property
(SI), central Jiang--Su plateau targets, pureness, and slice exhaustion of
the factor tracial quotient do not imply the mixed-source statement needed
by the capacity proof.

This is an abstract no-go, not a counterexample to XCIII.  It does not model
the actual faithful free-factor diagonal or prove that full-factor spectral
gap is useless beyond its established tracial-quotient consequence.
