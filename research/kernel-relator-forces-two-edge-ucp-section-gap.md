---
rg: 2
id: kernel-relator-forces-two-edge-ucp-section-gap
kind: claim
title: Every nontrivial triangle-kernel relator forces a quantitative two-edge gap for finite-face ucp sections
distinct_from:
  explicit-finite-face-ucp-section-is-edge-equivariant: that constructs an explicit section fixing either lifted edge exactly; this proves no section can approach both canonical edge lifts beyond a relator-length-dependent norm floor.
  triangle-relator-extension-admits-local-ucp-sections: that asks for local ucp sections of the full relator extension and allows all lifted values to move inside the kernel ideal; this only obstructs sections of the finite face quotient that try to preserve both canonical edge lifts.
  position-window-ucp-sections-collapse-to-folner-vectors: that obstructs a window-shaped construction over an infinite quotient by a scalar Folner argument; this is a finite-face operator-norm obstruction coming from multiplicative-domain defect and a kernel word.
---

**ESTABLISHED.**  In the triangle setting of
`triangle-colimit-llp-reduces-to-relator-local-splitting`, put

```text
E=P_1 *_(P_0) P_3,       q:E->>P_13,       N=ker q.
```

Let

```text
n=a_1 ... a_L in N\{1}
```

be a nontrivial reduced word with every `a_j in P_1 union P_3`.  Write

```text
v_j=u_(q(a_j)) in C^*(P_13),       w_j=u_(a_j) in C^*(E).
```

Then every ucp section `T:C^*(P_13)->C^*(E)` of the quotient `q_*` obeys

```text
max_(1<=j<=L) ||T(v_j)-w_j|| >= 2/L^2.                    (KUG1)
```

Proof: `kernel-relator-ucp-section-gap-proof`.

The bound is dimension-free and uses the full C-star norm.  Since the free
kernel `N` is torsion-free, every nontrivial relator has infinite order and
therefore `||1-u_n||=2`.  Thus no choice of finite-face section can become
simultaneously canonical on both generating sides.  In particular, the
right-`P_1`-equivariant and right-`P_3`-equivariant sections from
`explicit-finite-face-ucp-section-is-edge-equivariant` cannot be merged by a
small perturbation.

**Exact scope.**  This does not refute local splitting of
`C^*(G_0)->>C^*(Lambda)`.  A local section of the full quotient may send edge
unitaries to elements that differ by `O(1)` kernel-ideal corrections from the
canonical group unitaries.  The theorem rules out only the one-face strategy
that keeps the `P_12` and `P_23` lifts canonical while asking the finite
`P_13` section to repair the cycle.  Any positive construction must balance
the three face lifts simultaneously.
