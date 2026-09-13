---
rg: 2
id: hyperbolic-3-manifold-groups-in-paunescu-class
kind: claim
title: Every p.m.p. action of a lattice in PSL(2,C) is sofic
distinct_from:
  fpbs-hyperbolic-3-manifold-groups-fixed-price-one: that asks for fixed price of closed hyperbolic 3-manifold groups; this proves that all their p.m.p. actions are sofic, through the same virtual fibering
  paunescu-class-closed-under-amenable-extensions: that is the permanence theorem; this is its first substantial instance, a class of non-treeable groups with cost one that does not split over amenable subgroups
  sl3z-admits-nonsofic-action: that asks whether the higher-rank lattice SL3(Z) leaves Paunescu's class; this puts every rank-one lattice of PSL(2,C) inside it
---

**ESTABLISHED (unreviewed).** Let `Λ` be a lattice in `PSL_2(C)`, for instance the fundamental
group of a finite-volume hyperbolic 3-manifold. Then every p.m.p. action of `Λ` on a standard
probability space is sofic (Păunescu Definition 1.4); its crossed product embeds in `R^ω` with the
base in the diagonal and the group in permutations. The same holds for every group measure
equivalent to such a lattice.

**Proof sketch** (route `hyperbolic-3-manifold-groups-paunescu-class-proof`):
closed hyperbolic 3-manifolds virtually fiber (Agol), so a cocompact lattice is commensurable with
`π_1(S_g) ⋊ Z`; surface groups are amalgams of free groups over `Z`, hence in `𝒮`; extensions with
amenable quotient and finite-index overgroups stay in `𝒮`; lattices of one group are measure
equivalent.

**Why it is worth a node.** Before this, `𝒮` was known to contain amenable groups, treeable groups,
amalgams over amenable subgroups, their subgroups and commensurable groups. Closed hyperbolic
3-manifold groups are none of these: they have infimal cost `1` without being amenable, so they are
not treeable, and they do not split over amenable subgroups. They are also exactly the groups where
the percolation lanes work (`fpbs-hyperbolic-3-manifold-groups-fixed-price-one`).

**Scope.** This is a positive answer for rank one in `PSL_2(C)`. It says nothing about `SO(n,1)`,
`n >= 4`, whose lattices are not known to virtually fiber, or about higher-rank lattices.
