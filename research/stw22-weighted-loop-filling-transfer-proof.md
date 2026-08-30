---
rg: 2
id: stw22-weighted-loop-filling-transfer-proof
kind: route
title: Transfer uniform loop fillings between projection fibres and weighted purification fibres
target: stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling
requires:
  - stw22-low-spectrum-weighted-boundary-filling
artifacts:
  - research/artifacts/stw22-dimension-two-stiefel-filling-obstruction-audit-2026-08-30.md
---

Write `t=tau(e)` and let `delta_0=t-s>0`.

## Necessity

Take `a=p` in `(WPF)`.  Every element of `F(p)` is a partial isometry
with initial projection `p`, and its weighted metric is exactly the
ordinary `2`-norm metric:

```text
F(p)=V(p,e).
```

Consequently uniform equi-`LC^1` of all weighted fibres immediately
implies `(USF_1)`.  This also shows why proving contractibility separately
for each support trace cannot settle the issue.

## Sufficiency: discard the low spectral orientation

Assume `(USF_1)`.  Fix `epsilon>0`.  Choose `eta>0` so small that

```text
2 sqrt(eta s)<epsilon/4.                                (TF1)
```

Let `a` be as in `(WPF)`, write `p=supp(a)`, and split

```text
p_h=1_[eta,1](a),       p_l=p-p_h.
```

Suppose that `w:S^1->F(a)` is a loop contained in a `rho`-ball about
`w_0=v_0a^(1/2)`, and write `w(z)=v(z)a^(1/2)`.  On the high spectral
part,

```text
||v(z)p_h-v_0p_h||_2<=eta^(-1/2)||w(z)-w_0||_2.         (TF2)
```

Choose `rho` so that the right side is below the `(USF_1)` input modulus
for output radius `epsilon/4`.  The high-frame loop therefore has a
filling

```text
V_h:D^2->V(p_h,e)
```

which remains within `epsilon/4` in `2`-norm of `v_0p_h`.

## The remaining relative low-frame input

For `y in D^2`, the complement of the high range has trace

```text
tau(e-V_h(y)V_h(y)^*)=t-tau(p_h)
 >=tau(p_l)+delta_0.                                   (TF3)
```

The boundary weighted low frames

```text
z |-> v(z)a^(1/2)p_l
```

are continuous, but the polar frames `v(z)p_l` need not be continuous in
ordinary `2`-norm because eigenvalues of `a` can accumulate at zero inside
`p_l`.  Thus simple connectivity of a fixed strong Stiefel space cannot be
applied directly.  The exact required replacement is
`stw22-low-spectrum-weighted-boundary-filling`.  Assuming it, the boundary
weighted frames extend as `V_l(y)a^(1/2)p_l`, orthogonal to `V_h`, with

```text
V_l(y)^*V_l(y)=p_l.
```

Set

```text
W(y)=(V_h(y)+V_l(y))a^(1/2).
```

Then `W` fills the original loop in the exact fibre `F(a)`.  The high and
low spectral contributions are orthogonal in `L^2`; the high part costs at
most `epsilon/4`, while, regardless of how the low frame moves,

```text
||(V_l(y)-v_0p_l)a^(1/2)||_2
 <=2||a^(1/2)p_l||_2
 <=2 sqrt(eta s)<epsilon/4.                             (TF4)
```

Equations `(TF2)`--`(TF4)` give the asserted global metric-uniform
`epsilon`-small filling.  In particular they imply the ambient-local
equi-`LC^1` condition used by Michael.  Conversely, the global metric-
uniform weighted property restricted to projection fibres is exactly
`(USF_1)`, completing the stated equivalence.

The unweighted fixed-support modulus is now proved.  The remaining issue is
the weighted relative boundary-extension claim above; discontinuous low
polar frames cannot be substituted for it.
