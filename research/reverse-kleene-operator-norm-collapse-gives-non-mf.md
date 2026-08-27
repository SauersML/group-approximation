---
rg: 2
id: reverse-kleene-operator-norm-collapse-gives-non-mf
kind: claim
title: Reverse Kleene needs only an operator-norm collapse compiler for non-MF
distinct_from:
  reverse-kleene-involutive-compiler-gives-non-mf: that converts HS collapse through a wrapper; this is the strictly weaker MF-specific compiler.
  kleene-halting-mark-collapse-diagonal: that must control HS microstates; this only controls worst-direction operator norm.
---

If a computable compiler preserves a nontrivial word on halting instances
and forces it within operator-norm distance `<1` of the identity in every
small-defect tuple on nonhalting instances, reverse Kleene directly produces
a finitely presented non-MF group.  A finite disjunctive list of marks also
suffices by tensor-power separation and finite direct sums.
