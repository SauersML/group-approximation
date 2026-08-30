---
rg: 2
id: stw93-doubled-slice-has-capacity-one-proof
kind: route
title: Compute the hidden coordinate unit's capacity in the doubled Jiang--Su slice model
target: stw93-same-slice-si-does-not-force-central-capacity
requires:
  - stw93-saturated-slice-data-allow-residual-trace
  - stw93-property-si-holds-on-the-jiang-su-central-slice
artifacts:
  - research/artifacts/stw93-mixed-slice-capacity-audit-2026-08-30.md
---

Use the doubled model from
`stw93-doubled-fz-residual-trace-countermodel`.  It already proves pureness,
the trace-kernel formula, and slice exhaustion.  Let `e,f in G=F(Z)` be a
property-(SI) test pair.  Property (SI) for `Z` supplies `t in G` with

```text
t*t=e,                       ft=t.
```

Then `delta(t)` is a witness for the same-slice pair
`(delta(e),delta(f))` in `D_0`.  Thus the model retains precisely the
same-slice conclusion available in the actual XCIII algebra.

Now put `p=(0,1_G)`.  By the definition of
`I_0=J_(tau_G) direct_sum G`, one has `p in I_0`.  Plainly `[p]<=[1_(D_0)]`,
so its capacity is at least one.  If

```text
n[p]<=[1_(D_0)]
```

for some `n`, apply the lower-semicontinuous dimension function obtained by
composing the second-coordinate quotient with the unique normalized trace
of `G`.  It has value one on both `p` and `1_(D_0)`, and therefore gives

```text
n<=1.
```

Hence `cap_(D_0)(p)=1`.  For `0<epsilon<1`,
`(p-epsilon)_+=(1-epsilon)p` is Cuntz equivalent to `p`, so every nonzero
spectral cut has the same capacity.

The failure is exactly source placement: `p` lies outside the diagonal
Jiang--Su slice.  Same-slice `(SI)` says nothing about the pair `(p,f)`, even
when `f` is one of the orthogonal plateau targets used by
`stw93-orthogonal-z-targets-clone-kernel-cuts-proof`.
