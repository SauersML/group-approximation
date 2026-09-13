---
rg: 2
id: thompson-v-cyclic-subgroups-are-undistorted
kind: claim
title: Every infinite cyclic subgroup of the Higman--Thompson group V_n is undistorted
distinct_from:
  thompson-v-has-no-heisenberg-subgroup: that is the subgroup obstruction drawn from this theorem; this is the metric theorem itself, imported from the literature.
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that is a dynamical statement about almost automorphisms conjugate to proper powers; this is word-metric undistortion of every infinite cyclic subgroup of V_n.
---

**ESTABLISHED** by `thompson-v-cyclic-subgroups-are-undistorted-citation`.

Let `n >= 2` and let `alpha` be an element of `V_n` of infinite order. Then
`<alpha>` is undistorted in `V_n`: for a finite generating set `S` of `V_n`
there are `kappa > 0` and `C` with

```text
|alpha^m|_S >= kappa |m| - C      for all integers m.
```

Source: C. Bleak, H. Bowman, A. Gordon, G. Graham, J. Hughes, F. Matucci,
E. Sapir, *Centralizers in the R. Thompson group V_n*, arXiv:1107.0672v3,
Theorem 1.3, quoted in the citation route. `V = V_2`.

**Use in the graph.** Distortion of a central commutator is the standard
obstruction to embedding nilpotent groups. This theorem is the input of
`thompson-v-has-no-heisenberg-subgroup`, which is the firewall for the
Heisenberg question `leavitt-unit-group-has-no-integer-heisenberg-subgroup`
about the binary Leavitt unit group.
