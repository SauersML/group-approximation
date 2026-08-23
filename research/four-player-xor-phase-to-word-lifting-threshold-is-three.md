---
rg: 2
id: four-player-xor-phase-to-word-lifting-threshold-is-three
kind: claim
title: Four-player XOR phase refutations lift to group-word refutations exactly through three active questions
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
distinct_from:
  commuting-finite-phase-gadgets-have-affine-scalar-shadows: that is a general scalar-shadow no-go for commuting finite-phase packets; this gives a sharp finite XOR threshold at which an abelian incidence obstruction does or does not lift to an ordered noncommutative word.
  affine-auxiliary-control-flow-barrier: that fences affine auxiliary control flow in a predicate compiler; this distinguishes an integer phase obstruction from a true free-word refutation even though the local observables need not commute.
---

**THEOREM/FENCE (Tang--Zhu--Bai--Wang--Chen,
arXiv:2608.11139v1, Theorem 1.1 and Proposition 2.2).**  For every finite
four-player XOR game with at most three **active** questions per player,

```text
omega_co(G)=1
  iff G has a perfect GHZ-equatorial/MERP strategy.     (XPW1)
```

This is sharp.  The paper gives a four-player game with four active
questions per player for which `omega_co(G)=1` but no perfect MERP strategy
exists.

The exact compiler content is the distinction between two certificates.
A parity-permuted refutation specification (PREF) is an integer dependence
among clause-incidence rows with odd target parity.  It obstructs the
abelian MERP phase equations.  A **true refutation** additionally orders
the clause occurrences so that every player's question word freely
reduces to the identity; it is an actual group-word certificate.  The
dualities are

```text
no perfect MERP strategy  iff a PREF exists,
omega_co(G)<1             iff a true refutation exists. (XPW2)
```

At three active questions, every PREF lifts to a true refutation.  At four,
the Klein-four-group game has a PREF but no true refutation of any length,
order, or multiplicity.

Therefore an abelian phase inconsistency can be promoted to an ordinary
group-word inconsistency only with an additional lifting theorem; it is
not a formal rewriting step.  The four-question example is not presently
a finite-dimensional-versus-commuting separation: the paper explicitly
leaves open whether it has a perfect finite-dimensional non-MERP strategy.
