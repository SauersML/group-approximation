---
rg: 2
id: torsion-free-contractible-rips-complex-gives-type-f
kind: claim
title: A torsion-free group with a contractible Rips complex has a finite classifying space
distinct_from:
  hyperbolic-rips-complex-models-proper-actions: that is the theorem that Rips complexes of hyperbolic groups are contractible and model proper actions; this is the general consequence of contractibility for a torsion-free group, with no hyperbolicity
---

**ESTABLISHED** (route `torsion-free-contractible-rips-complex-gives-type-f-proof`).

Let `G` be a torsion-free group with finite generating set `S`, let `r >= 0`,
and suppose the Rips complex `P_r(G,S)` is contractible. Then the quotient
`P_r(G,S)/G` is a finite `K(G,1)`. In particular `G` is of type F, and
`cd G <= |B_S(r)| - 1`, where `B_S(r)` is the closed `r`-ball about `1`.

Equivalently, by contraposition: a torsion-free group of infinite cohomological
dimension, or more generally a torsion-free group that is not of type F, has no
contractible Rips complex over any finite generating set at any scale.
