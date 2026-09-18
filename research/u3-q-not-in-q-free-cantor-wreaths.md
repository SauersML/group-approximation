---
rg: 2
id: u3-q-not-in-q-free-cantor-wreaths
kind: claim
title: U_3(Q) embeds in no continuous wreath LC(C,H) x| Gamma with Gamma Q-free when the divisible subgroups of H are torsion-free and meet [H,H] in finitely generated groups, in particular not over its tower level U(Z,Z,Q)
distinct_from:
  q-free-normal-towers-omit-aff-q: that shows U_3(Q) has a three-step tower of normal subgroups with Q-free factors; this shows the last step of that tower cannot be realized as a continuous wreath over the middle level with a Q-free acting group.
  lifts-add-no-unipotent-divisibility: that excludes U_3(Q) from a central or covering lift of a Q-free group, which is the case H Q-free here; this allows fibres H that contain (Q,+), such as U(Z,Z,Q).
  twisted-bt-point-fixing-actor-elements-are-divisible: that constructs copies of Q and Q^k by cocycles over one coordinate and remarks that the device gives no U_3(Q); this proves a no-go theorem for a whole class of such cocycle constructions, including fibres with a rational centre.
  u3-q-embeds-in-fp-simple-group: that is the open stepping stone; this rules out one route to it.
---

**ESTABLISHED** through `u3-q-not-in-q-free-cantor-wreaths-proof`. Not
independently reviewed. No priority is claimed.

## Statement

Let `C` be a compact, metrizable, totally disconnected space and let
`Γ <= Homeo(C)` contain no subgroup isomorphic to `(Q,+)`. Let `H` be a group
such that

- (H1) every divisible abelian subgroup of `H` is torsion-free, and
- (H2) every divisible abelian subgroup of `H` meets `[H,H]` in a finitely
  generated group.

Let `E = LC(C,H) ⋊ Γ` be the group of bijections `(x,y) ↦ (γ(x), f(x)·y)` of
`C × H`, where `γ ∈ Γ` and `f : C -> H` is locally constant. Then the rational
Heisenberg group `U_3(Q)` does not embed in `E`.

**Main case.** Take `H = U_1 = U(Z,Z,Q)`, the unitriangular matrices with
integer `(1,2)` and `(2,3)` entries and rational `(1,3)` entry, and take
`Γ = V`.
- (H1) holds because the divisible subgroups of `U_1` lie in its centre
  `e_13(Q)`, as `U_1/Z(U_1) ≅ Z^2`.
- (H2) holds because `[U_1,U_1] = e_13(Z)`.

So `U_3(Q)` is not a continuous `V`-wreath over the middle level of its own
Q-free tower (`q-free-normal-towers-omit-aff-q`, item 3). Also
`U_1` does embed in twisted Brin--Thompson groups (the remark in that node).
Level-by-level rationalization therefore stops one step short of `U_3(Q)`.

Other fibres satisfying (H1) and (H2): `H_3(Z) × Q^k`, and every group whose
divisible abelian subgroups are torsion-free and central and whose commutator
subgroup is cyclic.

A Q-free fibre `H` may contain `Q/Z`, and then it fails (H1). That case is
covered separately: `LC(C,H)` is then Q-free (`q-free-normal-towers-omit-aff-q`),
so `lifts-add-no-unipotent-divisibility` applies to `E`.

## Consequence for the root

Inside a twisted Brin--Thompson group `SV_G`, fix a coordinate `*`. The elements
that act on `C_*` by `V` and on the other coordinates by a fibre group `Π`,
depending locally constantly on `x_*`, form a copy of `LC(C_*, Π) ⋊ V`.

A copy of `U_3(Q)` in such a subgroup would need a fibre group `Π` violating
(H1) or (H2). That means `Π` has torsion divisible subgroups, or rational
central elements that are commutators with unbounded denominators. Such a `Π`
already carries the divisible commutator structure that is sought. The fibres
built so far, `H_3(Z)` with a rationalized centre and the abelian rational
hulls of `twisted-bt-point-fixing-actor-elements-are-divisible`, satisfy (H1)
and (H2). So they cannot be extended to `U_3(Q)` by one more cocycle level
over a single `V`-coordinate. `U_3(Q)` inside `SV_G` or `nV` needs elements
that entangle `V`-coordinates, consistent with
`rational-stepping-stones-in-nv-need-bs12-or-heisenberg`.
