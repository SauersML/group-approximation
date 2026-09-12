---
rg: 2
id: sl2-s-arithmetic-noncentral-normal-subgroups-have-finite-index
kind: claim
title: Every non-central normal subgroup of SL2 of the p-integers has finite index, so the normal closure of any unipotent power is of finite index
distinct_from:
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that consumes this fact in one sentence ("the normal closure of u^N has finite index") to conclude that finite-dimensional unitary representations have finite image; this is the literature import itself, isolated because its analogue is FALSE for SL_2(Z).
  arithmetic-pair-group-factor-ultrapower-has-no-leak: that uses Borel density to show non-central elements have infinite-index centralisers in SL_n(Z); this is the stronger normal-subgroup statement for the ambient S-arithmetic group, a Margulis-theorem import.
---

**Literature input (source-level statement).**  Let `p` be a prime and
`Gamma = SL_2(Z[1/p])`.  Then every normal subgroup of `Gamma` is either
central (contained in `{+-1}`) or of finite index.  Consequently, for
every `N >= 1` and every non-central `g in Gamma` -- in particular for
the unipotent power `u^N`, `u = [[1,1],[0,1]]` -- the normal closure
`<<g>>` has finite index in `Gamma`; by Serre's congruence subgroup
property it then contains a principal congruence subgroup of level prime
to `p`.

**Sources.**  `Gamma` is an irreducible lattice in
`SL_2(R) x SL_2(Q_p)`, a semisimple group of rank `1 + 1 = 2` (Borel,
Harish-Chandra; Borel's theorem on S-arithmetic subgroups).  Margulis'
normal subgroup theorem for irreducible lattices in products of rank at
least two (G. A. Margulis, *Discrete subgroups of semisimple Lie groups*,
Springer 1991, Chapter IV, Theorem 4.9, which covers products of real and
`p`-adic groups) says every normal subgroup is finite or of finite index;
a finite normal subgroup of a lattice in a group with no compact factors
is central.  The congruence form is J.-P. Serre, *Le problème des groupes
de congruence pour SL_2*, Ann. of Math. 92 (1970), together with
Bass--Milnor--Serre; this is the route Peterson--Thom take in the proof of
their Theorem 2.6 (arXiv:1303.4007), which is how the graph first cited
it.

**Why this needs its own node.**  The statement is specific to the
`S`-arithmetic (infinitely-many-units) situation and FAILS for the
subgroup `SL_2(Z)`: the normal closure of `u^N` in `PSL_2(Z)` is the
kernel of the quotient onto the `(2, 3, N)` triangle group, which is
infinite for `N >= 7`, so that normal closure has infinite index.  A
reader who treats the import as routine could silently transfer it to
`SL_2(Z)` and break the co-density argument.
