---
rg: 2
id: triangle-lifts-avoid-both-tree-anchor-faces
kind: claim
title: Approximate triangle lifts stay uniformly away from both scalar and canonical tree anchors
distinct_from:
  scalar-tree-perturbations-linearly-control-closing-face: that proves metric subregularity of the scalar-tree compatibility face for every ucp map; this combines it with quotient accuracy and the independent kernel-cycle Gram floor for the explicit triangle.
  three-face-ucp-balancing-needs-macroscopic-tree-motion: that gives distance from the canonical tree-word lift without any quotient condition; this adds a second, scalar-tree exclusion forced by approximate right-invertibility.
  finite-packet-triangle-repair-is-ideal-block-choi-feasibility: that describes a packetwise affine Choi intersection after applying a finite-dimensional representation; this concerns actual ucp maps into the extension algebra, where the nontrivial kernel word and quotient norm remain visible.
---

**ESTABLISHED (two-anchor transversality for the explicit triangle).**  Use
the explicit `(3,3,4)` triangle, let

```text
q:A=C^*(G_0)->>Q=C^*(Lambda),
S_Delta=B_12+B_23+B_13,
r_0=||id_(B_13)-E_epsilon^Q|_(B_13)||_cb>0,               (TAT1)
```

and retain `C_Delta=|P_13|R_13^2` from the linear scalar-tree modulus.  For a
ucp map `Phi:S_Delta->A`, put

```text
zeta(Phi)=||q o Phi-incl_(S_Delta)||_cb,
eta(Phi)=max_(V=P_12,P_23)
 ||Phi|_(C^*(V))-E_epsilon^A|_(C^*(V))||_cb.              (TAT2)
```

Then

```text
eta(Phi)>=max{0,r_0-zeta(Phi)}/C_Delta.                   (TAT3)
```

Independently, for the fixed nontrivial reduced kernel word
`n=a_1...a_L`, with `v_j=u_(q_E(a_j))` and `w_j=u_(a_j)`,

```text
max_j ||Phi(v_j)-w_j||>=2/L^2.                            (TAT4)
```

In particular, every `zeta<=r_0/2` approximate local lift satisfies both

```text
eta(Phi)>=r_0/(2C_Delta),
max_j ||Phi(v_j)-w_j||>=2/L^2.                            (TAT5)
```

Thus the approximate-lifting Choi slice has a fixed neighborhood disjoint
from the scalar-tree face and, simultaneously, a fixed neighborhood disjoint
from the canonical tree-word lift.  There is no triangle-respecting tangent
curve of increasingly accurate ucp lifts converging to either anchor.

**Exact scope.**  This is a genuine triangle-specific error bound, but not a
proof that the lifting Choi slice is empty.  A noncanonical balance can live
macroscopically far from both anchors.  Nor does `(TAT3)` convert the dual
component `c_13` into a primal displacement; it applies after an approximate
lift has been constructed.  The remaining uniform-reservoir problem is to
construct or exclude precisely that middle region of the Choi cone.

Proof: `combine-the-overlap-error-bound-with-the-kernel-gram-floor`.

DERIVATION
combine-the-overlap-error-bound-with-the-kernel-gram-floor
