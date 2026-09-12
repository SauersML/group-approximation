---
rg: 2
id: torsion-free-central-cover-forces-abelian-finite-subgroups
kind: claim
title: A group with a torsion-free central cover has only abelian finite subgroups
distinct_from:
  free-abelianized-cover-is-torsion-free: that constructs a torsion-free cover with abelian, generally noncentral, kernel over an arbitrary group; this proves that demanding the kernel be CENTRAL makes such a cover impossible over any group with a nonabelian finite subgroup.
  finite-torsion-carrier-virtual-torsionfree-criterion: that decides virtual torsion-freeness of one group by a finite-quotient test on its finite subgroups; this decides which groups can carry a torsion-free central extension above them, and involves no finite quotient.
  torsion-generated-mf-absorbers-die-in-torsion-free-targets: that kills homomorphisms out of a torsion-generated group into a torsion-free target; this kills central extensions with torsion-free total group over a target with nonabelian finite subgroups, and its input is a finite subgroup, not a generating set.
artifacts:
  - research/artifacts/torsion-free-transfer-covers-and-obstructions-2026-09-08.md
---

**ESTABLISHED.**  Let

```text
1 -> A -> E -> G -> 1                                                   (CC1)
```

be a central extension with `E` torsion-free.  Then **every finite subgroup
of `G` is abelian**.

**Consequence for transfers.**  There is no procedure taking an arbitrary
non-MF group to a torsion-free non-MF group by passing to a central cover.
Given any non-MF `G_0`, the group

```text
G = G_0 x S_3
```

is again non-MF, because it contains `G_0` and MF passes to subgroups
(`mf-positive-controls`), and `G` has the nonabelian finite subgroup `S_3`.
By the theorem no torsion-free group surjects onto `G` with central kernel.
So the entire class of central-cover procedures fails on inputs that are
freely available, whatever the input's own torsion.

This is an obstruction to one class of procedures, not an impossibility
theorem for transfers.  Abelian noncentral kernels are not touched: the
cover of `free-abelianized-cover-is-torsion-free` exists over every group,
including `G_0 x S_3`, and its kernel is abelian but acts nontrivially.
