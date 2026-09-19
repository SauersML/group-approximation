---
rg: 2
id: atlas-a4-classical-opaque-star-sharp-constant
kind: claim
title: The collision-assisted opaque star has sharp constant one over square-root two on every classical alignment mixture
artifacts:
  - experiments/atlas_a4_opaque_star_regular_screen.py
distinct_from:
  atlas-a4-packet-alone-fails-opaque-star: that exhibits one packet-only spectral mismatch and proves collision is necessary; this computes the exact collision-assisted ratio on all sixty alignment sectors and their arbitrary direct sums.
  atlas-a4-collision-assisted-opaque-star-compiler: that asks for the estimate on arbitrary growing matrix-valued multiplicity holonomy; this proves it only on the complete classical alignment simplex and isolates why the finite calibration does not extend formally.
---

Let `alpha` be any of the thirty inner or thirty outer chart alignments which
satisfy all thirty shortest A4 packet words exactly.  In `Reg(A8)`, put

```text
V_alpha(t)=lambda(alpha(t)t^-1),
T={t01,t12,t23,t30},       b=t23,
q_alpha=q_19243(alpha).
```

Then

```text
max_(t in T-{b}) inf_(A unitary)
  ||V_alpha(t)-A V_alpha(b) A^*||_2
 <= (1/sqrt(2)) ||lambda(q_alpha)-1||_2,               (A4-CL-STAR)

||V_alpha(b)-1||_2
 = ||lambda(q_alpha)-1||_2.                            (A4-CL-HUB)
```

The constant `1/sqrt(2)` in `(A4-CL-STAR)` and the constant one in
`(A4-CL-HUB)` are both sharp.  Moreover the same constants hold for arbitrary
finite direct sums and external amplifications of the sixty alignment
sectors.

The exact screen gives more detail.  Twenty-two of the thirty inner sectors
and twenty of the thirty outer sectors attain the nonzero transport gap.  A
first inner extremizer is

```text
alpha=00000100010000000001000000000001,
(ord V(t01),ord V(t12),ord V(t23),ord V(t30))=(4,4,2,2),
```

while a first outer extremizer has profile `(2,2,4,4)` at the same displayed
matrix.

This is a dimension-free theorem on the classical alignment simplex, not a
proof of the full compiler.  The four rectangle holonomies leave two
independent packet-component root gauges.  As recorded in
`atlas-a4-two-holonomy-reflection-energy-ceiling`, changing the `H_6` root
gauge preserves all four rectangles and the collision residual while changing
a cross-component endpoint.  Therefore the sharp finite constant cannot be
promoted from rectangle data alone.  A general extension must retain the
common-`U` liftability constraint; no amplification counterexample satisfying
that constraint is produced here.
