---
rg: 2
id: decidable-group-algebras-embed-in-fp-central-simple-algebras
kind: claim
title: Every decidable group algebra over F_2 embeds unitally in a finitely presented central simple F_2-algebra, with no K-theory condition
distinct_from:
  decidable-group-algebras-have-fp-central-simple-hosts: that adds K_1 = K_2 = 0 of B ⊗ L_2; this drops the K-condition, which a Cuntz swindle factor supplies separately.
  algebra-boone-higman-conjecture: that embeds every decidable algebra in a finitely presented simple algebra; this treats only group algebras over F_2, and asks in addition for centre F_2.
  simple-inputs-have-fp-essential-shell-germ-algebras: that asks for finite presentation of the specific algebra A_nu/J of a shell envelope; this allows any finitely presented central simple host.
  decidable-group-algebras-have-fp-cantor-crossed-hosts: that asks for a host of the specific form LC(X, F_2) ⋊ P, with K-theory from Farrell–Jones; this asks for any finitely presented central simple host.
  group-algebras-embed-in-shell-essential-algebras: that gives a central simple host A_nu/J for every countable group, without finite presentation; this asks for finite presentation when the word problem is solvable.
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem. Then there is a
finitely presented unital `F_2`-algebra `B` that is simple with centre `F_2`, together with a
unital injective algebra map `F_2[G] -> B`.

## Role

This is the input-dependent hole of `fp-central-simple-hosts-via-cuntz-swindle-factor`. That
route adds `fp-central-simple-cuntz-swindle-algebra-exists`, which does not depend on `G`, and
together the two give `decidable-group-algebras-have-fp-central-simple-hosts`. No K-theory
condition is needed here.

## How it can fail independently

- It is implied by `algebra-boone-higman-conjecture` over `F_2` for group algebras, provided the
  simple envelope can be taken with centre `F_2`. A central simple envelope is needed, because the
  centre of an fp simple `F_2`-algebra is a field, and it can be larger than `F_2`.
- It is implied by `simple-inputs-have-fp-essential-shell-germ-algebras`, applied to a
  finitely generated infinite perfect overgroup `P` of `G` with solvable word problem, whenever
  one is available (for instance a finitely generated simple overgroup with solvable word
  problem). Then
  `F_2[G] <= F_2[P] <= A_nu/J`, and the second inclusion is
  `group-algebras-embed-in-shell-essential-algebras`.
- A decidable `G` such that no finitely presented central simple algebra contains `F_2[G]`
  unitally would refute it. None is known.
- If it holds but `fp-central-simple-cuntz-swindle-algebra-exists` fails, the K-gate returns
  and this claim alone gives no simple group.
