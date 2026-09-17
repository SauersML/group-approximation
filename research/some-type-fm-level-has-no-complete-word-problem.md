---
rg: 2
id: some-type-fm-level-has-no-complete-word-problem
kind: claim
title: "For some finite m >= 3, no group of type F_m has an r.e.-complete word problem"
refuted_by:
  - some-type-f-group-has-re-complete-word-problem
---

There is a finite `m >= 3` such that the word problem of every group of type
`F_m` is not complete among recursively enumerable sets under many-one
reductions.

This is the premise of `no-type-fn-plus-1-host-via-word-problem-degree`, which
derives the negative answer to the first part of Zaremsky Problem 1.1. It is
the sharp form of the word-problem obstruction strategy.

## Attempts

- **Expected false; the source must be checked.** A group of type `F` whose
  word problem is r.e.-complete refutes this claim at every level `m`. Collins
  and Miller produce a group of type `F` with unsolvable word problem (note to
  Problem 1.2 of Zaremsky's list). Novikov--Boone-type constructions encode the
  halting set into special words, so a many-one reduction from the halting set
  is plausible. Whether their group realises the complete degree has not been
  checked at the source; that check decides this claim.
- **Self-host of `U` is circular.** The universal finitely presented group `U`
  has an r.e.-complete word problem. Refuting this claim with `U` needs a host
  of `U` of type `F_m`, which is the problem itself.
- **An `F_∞` analogue** ("no group of type `F_∞` has an r.e.-complete word
  problem") would give only `some-finitely-presented-group-embeds-in-no-f-infinity-group`.
  It is not recorded as a node.
- **Refuted (sw-117, 2026-09-17).** The Aanderaa--Cohen--Boone group `G_M` of the
  machine-checked Novikov--Boone chain is of type `F`
  (`boone-final-group-is-of-type-f`: the associated subgroup of the last stable
  letter is free on `t, r_1, ..., r_n`, then Scott--Wall), and the chain's machine
  runs the universal partial recursive function on a fixed input, whose halting
  set is m-complete by s-m-n. So `K <=_m WP(G_M)` and `G_M` has r.e.-complete
  word problem: `some-type-f-group-has-re-complete-word-problem`. The claim fails
  at every level, and the premise of `no-type-fn-plus-1-host-via-word-problem-degree`
  is false.
