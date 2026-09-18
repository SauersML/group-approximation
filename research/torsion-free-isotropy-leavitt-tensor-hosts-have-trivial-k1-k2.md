---
rg: 2
id: torsion-free-isotropy-leavitt-tensor-hosts-have-trivial-k1-k2
kind: claim
title: If every finite subgroup of a finitely generated group acts freely on a compact zero-dimensional space, the Leavitt tensor of the binary crossed product has trivial K_1 and K_2
distinct_from:
  free-action-leavitt-tensor-hosts-have-trivial-k1-k2: that is premise (K), for free actions; this is premise (K′), which needs freeness only of finite subgroups, so (K′) implies (K).
  farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts: that proves (K′) in every degree when the acting group satisfies Farrell-Jones; this is the statement for every finitely generated acting group.
  free-crossed-leavitt-k-gate-is-a-farrell-jones-instance: that shows (K′) for a given acting group is equivalent to one Farrell-Jones instance; this records (K′) as the premise the relaxed route consumes.
---

**OPEN.** Premise (K′) of `boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts`
(lane bh-g3-topfree, 2026-09-18).

## Statement

Let `Λ` be finitely generated and act on a compact Hausdorff zero-dimensional space `X`, so that no
nontrivial element of finite order has a fixed point. Let `B = LC(X, F_2) ⋊ Λ` and
`L = L_(F_2)(1,2)`. Then `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`.

## Status

- **Established for Farrell–Jones `Λ`**, torsion allowed, in every degree
  (`farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts`).
- **Established for torsion-free Farrell–Jones `Λ` and every action**
  (`cantor-crossed-product-leavitt-tensors-are-k-trivial`).
- **For a given `Λ`**, (K′) is equivalent to one Farrell–Jones instance with coefficients
  `LC(X, L)` (`free-crossed-leavitt-k-gate-is-a-farrell-jones-instance`, whose setting is exactly
  this hypothesis).
- **The hypothesis is sharp.** `Z/2` acting trivially has `K_1 ≠ 0`
  (`leavitt-tensor-k1-sees-traces-of-nilpotent-matrices`).

## Lesson for general BH

The K-gate cares only about finite-order isotropy. Infinite cyclic point stabilizers, which every
boundary-type shift has, cost nothing. So the relaxation to topologically free shifts in
`master-route-needs-only-topological-freeness` leaves the K-gate exactly as hard as before: one
Farrell–Jones instance for the acting group.
