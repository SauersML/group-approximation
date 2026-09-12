---
rg: 2
id: bass-serre-edge-rigidity-kills-independent-kernel-gauges
kind: route
title: Use an A2-A2 self-normalizing edge to collapse two tree-face kernel gauges and apply the cycle Gram floor
target: kernel-inner-tree-face-balancing-collapses
requires:
  - simple-kazhdan-kac-moody-lattices-exist
  - triangle-colimit-llp-reduces-to-relator-local-splitting
  - three-face-ucp-balancing-needs-macroscopic-tree-motion
---

Use the explicit matrix `(IK1)`.  The two tree vertices adjacent to `P_2`
are finite type `A_2`, in which the standard rank-one subgroup `P_2` is
self-normalizing.  On the Bass--Serre tree of
`P_12 *_(P_2) P_23`, this makes the fundamental edge the entire `P_2`-fixed
subtree, hence `C_(G_0)(P_2)<=P_2`.

If the two tree-face embeddings are conjugated by `k_12,k_23` in the quotient
kernel, agreement on the shared face says that `k_23^(-1)k_12` centralizes
`P_2`.  The quotient is injective on `P_2`, so this element is trivial.  The
two conjugations are one common global conjugation.  Remove it from the ucp
map; both tree faces become canonical, contradicting the kernel-cycle Gram
floor.  Therefore at least one tree-face restriction in any possible local
section is not an inner conjugate of its canonical embedding.
