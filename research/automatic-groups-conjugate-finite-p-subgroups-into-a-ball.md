---
rg: 2
id: automatic-groups-conjugate-finite-p-subgroups-into-a-ball
kind: claim
title: In every automatic group the finite p-subgroups have bounded order and lie in finitely many conjugacy classes
distinct_from:
  torsion-free-automatic-groups-have-finite-cd: that is the dimension half of what a contractible Rips complex forces; this is the independent torsion half, forced through Smith theory, and it says nothing about torsion-free groups
  automatic-groups-have-contractible-rips-complexes: that is the full open claim; this is a necessary condition for it which can fail on its own, and whose failure would refute it
  bvc-groups-have-bounded-finite-subgroups: that is the corresponding finiteness for groups with property BVC; this is the open statement for automatic groups, restricted to prime-power order
---

**OPEN.** Let `G` be automatic. Then there are a finite generating set `S` and
`d >= 1` such that every finite subgroup `P <= G` of prime-power order is conjugate
into the ball `B_S(d)`. In particular `G` has finitely many conjugacy classes of
finite subgroups of prime-power order, and their orders are bounded.

It follows from `automatic-groups-have-contractible-rips-complexes` (route
`automatic-p-subgroup-ball-via-rips`), with the same `S` and `d`.

**What it is for.** The target `automatic-groups-have-contractible-rips-complexes`
has two necessary conditions, and each can fail without the other.

- Dimension: every torsion-free subgroup has cohomological dimension at most
  `|B_S(d)| - 1`. This covers `torsion-free-automatic-groups-have-finite-cd`.
- Torsion: this claim.

So a refutation of the target does not need a group of infinite dimension like `F`.
An automatic group with finite `2`-subgroups of unbounded order, or with infinitely
many conjugacy classes of `p`-subgroups, would already refute it. Thompson's `T`
shows the torsion invariant bites among `F_∞` groups with asynchronous combings
(`weak-automaticity-does-not-give-contractible-rips-complexes`).

## Attempts

- 2026-09-17 (swarm-0917-w4-z-rips): **status search.**
  - For biautomatic groups the statement holds for all finite subgroups (Gersten–Short
    1991, from memory, not re-read). The biautomatic proof uses fellow travelling
    of both left and right translates of normal forms.
  - For automatic groups a finite subgroup `P` acts on the left. An automatic
    structure only controls right multiplication by generators, so `p·w_g` and
    `w_(pg)` are not known to fellow travel, and the centring argument does not
    start.
  - Web searches found no proof or counterexample for automatic groups. The Brady–
    Clay–Dani abstract (arXiv:0709.3802) lists hyperbolic, CAT(0), mapping class
    groups, `Aut(F_n)`, `Out(F_n)` and arithmetic groups as having the property, in
    the summarizing fetch. Automatic groups were not in that list.
  - Every standard automatic class checked has finite virtual cohomological
    dimension, and so satisfies the claim by the same Smith argument applied to a
    finite-dimensional model: hyperbolic, cocompactly cubulated, Coxeter, spherical
    Artin, mapping class groups. That check is from memory, not a literature search.
