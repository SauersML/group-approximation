---
title: STW LXVI dyadic Rordam V4 audit --- identical pairing fails Hall on the infinite seed (2026-08-30)
---

## Verdict

The private-coordinate induction in (V4) is false, and no corrected
finite size bound `h(n)` can repair it within the stated architecture.
At every identical paired step there is already a finite sublist violating
Hall's condition.

## The overlooked collision multiplicity

Fix one branch at every stage preceding a paired step and follow this same
history from every singleton seed `{a_i}`.  Because all evaluation sets are
finite, all but finitely many seed coordinates survive the history.  The
resulting sets have the exact shape

`J_i = C union {u_i}`,

where `C` is the finite collection of coordinates introduced by the fixed
branch history and the `u_i` are pairwise distinct.  Thus only `u_i` is
private to seed `i`; every coordinate supplied by an `I`-set is common to
all infinitely many seeds following that history.  Fresh relabeling ranges
separate different branches, not different seeds using the same branch.

At a paired step, choose one duplicated branch.  Its two identical copies
send each good `J_i` to two copies of

`K_i = C' union {v_i}`.

For `N>|C'|`, the sublist consisting of both copies for `N` seeds has
length `2N` and union size `N+|C'|<2N`.  This is an explicit violation of
the list form of Rordam Proposition 3.2.

## Why the proposed repairs do not work

* Slowing the paired schedule is irrelevant: the argument applies to the
  first paired step.
* Increasing `h(n)` is irrelevant: every `I`-set remains finite, and one
  chooses more seed indices than the resulting common finite tail.
* Distinct relabelings on nonpaired branches are irrelevant: the bad
  sublist follows one fixed history and then one identical branch pair.
* Calling the new coordinates "private per copy" is the precise error.
  The two copies have equal sets, and their tensor coordinates are also
  shared across all seed summands following the same history.

The claimed sufficient invariant would have to provide private capacity
per **seed occurrence**, not per branch.  The stated maps provide only one
such coordinate per surviving singleton seed, while a duplicated branch
demands two representatives per seed asymptotically.  Any genuine repair
therefore needs parent-dependent coordinate blocks (or a fundamentally
different Euler/finiteness argument), not a larger finite branch-common
block.

This obstruction is earlier and more elementary than the existing
late-stage rank/dimension proof in
`uniformly-doubled-rordam-steps-force-proper-infiniteness`: it refutes the
(V4) certificate directly, without asserting proper infiniteness of the
limit.
