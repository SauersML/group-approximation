---
rg: 2
id: no-decidable-group-contains-every-polynomial-dehn-fp-group
kind: claim
title: No finitely generated group with solvable word problem contains every finitely presented group with Dehn function n^18
distinct_from:
  no-decidable-group-contains-every-fp-rf-group: that excludes a decidable host for all finitely presented residually finite groups by pitting the host's own time bound against arbitrarily hard inputs; this excludes a decidable host for a class whose members all have ONE complexity bound, so no complexity count can work, and the obstruction is uniformity instead.
  complexity-bounded-host-classes-are-not-universal: that says hosts sharing a time bound miss some harder input; this says a decidable host misses some input even when every input shares a time bound, which refutes the survival "one host per family with a uniform complexity bound" recorded in no-decidable-group-contains-every-fp-rf-group.
  uniform-hosts-force-uniform-word-problem: that is the general transfer from hosts to uniform decision; this is its application to the halting-indexed BORS family.
---

**ESTABLISHED (unreviewed).**  Let `U` be a finitely generated group with
solvable word problem.  Then `U` fails to contain an isomorphic copy of at
least one group in each of the following classes:

1. the finitely presented groups whose Dehn function is `≼ n^18`;
2. the finitely presented groups whose word problem, on the given generators,
   is decided by a deterministic Turing machine in time `<= 2^((n+1)^37)`;
   the bound is exact, with no `≼` constants;
3. for `T(n) = 2^((n+1)^37)`, the finitely generated groups with word problem
   in `F(T)`, the languages decidable in time `C T(Cn) + Cn + C`.

The missed group can be taken among the `H_e` of
`polynomial-dehn-fp-groups-have-nonuniform-word-problem` with `phi_e(0)`
divergent.  For these, `H_e` contains `F_2` with bounded distortion.

Every group in these classes has solvable word problem, and each class has one
recursive complexity bound for all its members.  So the programme "one
decidable host per complexity class" fails already at an elementary bound.
This refutes the survival clause "per family with a uniform complexity bound"
of `no-decidable-group-contains-every-fp-rf-group`, and the premise
`complexity-graded-universal-decidable-hosts-exist`.

**Where the obstruction sits.**  It is not the complexity of any input.  By
`complexity-bounded-host-classes-are-not-universal`, `U` has some recursive
bound `t`, and here `t` may be far above `T`.  The obstruction is that a
single host turns membership of the family into a uniform decision procedure,
by `uniform-hosts-force-uniform-word-problem`.  The family can hide the halting
time of `phi_e(0)` in constants that no complexity class records.

DERIVATION
no-decidable-group-contains-every-polynomial-dehn-fp-group-proof
