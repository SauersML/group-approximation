---
rg: 2
id: f3-hosts-for-fp-groups-via-rope-trick-over-fp2-host
kind: route
title: "Dead: use a (twisted) rope-trick container of a universal group over a host with finite rational H_2 as the F_3 host"
target: every-finitely-presented-group-embeds-in-an-f3-group
requires: []
---

**Dead route**, recorded so the attempt stays visible. It is killed by
`twisted-rope-trick-container-is-not-fp3-over-fp2-hosts` through that claim's
`invalidates:`.

The attempt:
- Write a universal finitely presented group as `U = F/R`, take the double
  `L = F_1 *_R F_2`, and choose injective homomorphisms `ι, ι': L → P` into a
  finitely presented host.
- The container `Hig_{ι,ι'}(U)` is finitely presented
  (`twisted-rope-trick-embeds-g-in-a-finitely-presented-group`) and contains
  `U`.
- If it were of type `FP_3`, it would be an `F_3` host of every finitely
  presented group.

Why it dies: `U` is infinite and `R ≠ 1`. If `ι' = ι`, or more generally
`H_2(ι) = H_2(ι')`, over any finitely generated `P`, or if `H_2(P; Q)` is
finite-dimensional whatever `ι, ι'` are, then `H_3(Hig_{ι,ι'}(U); Q)` is
infinite-dimensional, so the container is not of type `FP_3(Q)`. The untwisted
case is Theorem B of Fournier-Facio–Zaremsky arXiv:2607.21727v1.

The case not killed is a host with infinite rational `H_2` on which the two
embeddings differ essentially injectively. It is recorded as the open claim
`acyclic-host-twisted-rope-container-is-of-type-fp3`.
