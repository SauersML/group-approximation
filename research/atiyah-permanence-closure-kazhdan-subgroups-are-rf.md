---
rg: 2
id: atiyah-permanence-closure-kazhdan-subgroups-are-rf
kind: claim
title: Kazhdan subgroups of the Strong Atiyah permanence closure are residually finite, so the torsion-free master host lies outside it
distinct_from:
  lea-permanence-closure-fp-kazhdan-groups-are-residually-finite: that closes the LEA groups under amenable-quotient extensions and needs finite presentation; this closes residually finite and T-finite groups, such as locally indicable groups, under extensions with T-finite quotient over arbitrary kernels and under residual systems, and applies the result to Strong Atiyah at the torsion-free master host.
  kazhdan-groups-in-sofic-permanence-closure-are-lef: that is the sofic closure of amenable and LEF groups with marked limits and concludes LEF; this is the Strong Atiyah closure, whose locally indicable base and locally indicable quotients over nonsofic kernels are not known to preserve soficity, and it concludes residual finiteness.
  universal-torsion-free-hosts-not-sofic-or-locally-indicable: that excludes the master host from the sofic, locally indicable and Linnell classes; this excludes it from the closure of the residually finite and T-finite groups, which contain the recorded proved Strong Atiyah classes, under all the recorded permanence operations, including the open Kazhdan-edge amalgam permanence.
  atiyah-kazhdan-edge-blocks-both-permanence-routes: that explains why two proof frameworks fail for one amalgam over a Kazhdan edge; this shows that even granting permanence over every edge, no permanence argument of this shape reaches the master host.
artifacts:
  - research/artifacts/atiyah-permanence-closure-kazhdan-rf-2026-09-16.md
---

**ESTABLISHED (unreviewed)** by [[atiyah-permanence-closure-kazhdan-rf-proof]].

Call a group **T-finite** if all its subgroups with property (T) are finite.
Let `T` be the class of groups all of whose finitely generated subgroups with
property (T) are residually finite.

1. **Closure.**  `T` contains every residually finite group and every T-finite
   group.  It is closed under:
   - (C1) subgroups;
   - (C2) directed unions;
   - (C3) fundamental groups of graphs of groups with vertex groups in `T`,
     for any graph, edge groups and edge maps;
   - (C4) extensions `N ⊴ G` with `N` in `T` and `G/N` T-finite;
   - (C5) finite direct products;
   - (C6) residual systems: normal subgroups `N_i` with trivial intersection
     and every `G/N_i` in `T`.

   So for every class `Y <= T`, the closure `A(Y)` of `Y` under (C1)--(C6) is
   contained in `T`.
2. **A torsion-free witness outside `T`.**  Let `n >= 2`, `p: G~ -> Sp_2n(R)`
   the universal cover, `Gamma' = ker(Sp_2n(Z) -> Sp_2n(Z/3Z))` and
   `Lambda = p^-1(Gamma')`.  Then `Lambda` is finitely presented, torsion-free,
   Kazhdan and not residually finite, so it is not in `T`.
3. **The master host.**  No group containing a copy of `Lambda` lies in `T`.
   In particular the group `E` of
   `two-generator-fp-torsion-free-universal-whitehead-container`, the host of
   `master-host-satisfies-algebraic-strong-atiyah`, is not in `A(Y)` for any
   `Y <= T`.

## What `A(Y)` covers

- **Base classes in `T`.**
  - residually finite groups, including all subgroups of torsion-free compact
    `p`-adic analytic groups and the congruence Kazhdan groups;
  - amenable groups, locally indicable groups and residually torsion-free
    elementary amenable groups, which are T-finite.

  The artifact proves these memberships.  Residual finiteness of virtually
  compact special, braid, 3-manifold, mapping class and `Out(A_Gamma)` groups
  is only recalled there.
- **Operations.**
  - Linnell's class `C` lies in `A(RF)`.
  - The torsion-free elementary amenable and the locally indicable extension
    theorems, with arbitrary kernels, are instances of (C4).
  - Graphs of groups with finite edge groups, and the OPEN amalgam permanence
    `strong-atiyah-kazhdan-edge-amalgam-permanence`, are instances of (C3).
  - Finite-index overgroups follow from (C1) and (C4), and approximation by
    residual systems of quotients from (C6).

So a proof of `master-host-satisfies-algebraic-strong-atiyah` by permanence
must use an operation under which `T` is not closed.

**Sharpness.**  `T` is not closed under central extensions with kernel `Z`
and residually finite Kazhdan quotient: `Lambda` is such an extension of
`Gamma'`, and `Gamma'` satisfies Strong Atiyah
(`p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`, since
`Gamma' <= CS(1,2n,3)`).  The resulting necessary test case is
`deligne-torsion-free-lattice-satisfies-strong-atiyah`.

**Scope.**  This is an obstruction to permanence arguments only.  It does not
decide Strong Atiyah for `E` or `Lambda`, and it does not constrain direct
constructions of a division ring between `Qbar[E]` and `U(E)`.

**Credit.**  The inductive pattern is the one in
`lea-permanence-closure-fp-kazhdan-groups-are-residually-finite` and
`kazhdan-groups-in-sofic-permanence-closure-are-lef`: property (T) gives a
fixed vertex (Watatani) and kills infinite T-finite images.  This node changes
the base classes and the extension hypothesis, adds residual systems and
arbitrary Kazhdan subgroups, and applies the result to the Strong Atiyah host.

Item 3 does not need `Lambda`.  The graph already records finitely presented,
torsion-free, Kazhdan, non-residually-finite groups: the Titz Mite--Witzel
lattices (`titz-witzel-simple-kazhdan-cat0-lattices-exist`), and the
Fournier--Facio group as used in
`universal-torsion-free-host-obstruction-proof`.  Either one embeds in `E` and
gives item 3.  What `Lambda` adds is an explicit witness in which kernel and
quotient both satisfy Strong Atiyah, which isolates the missing operation
(see **Sharpness**).
