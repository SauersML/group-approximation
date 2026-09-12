---
rg: 2
id: tester-host-has-positive-rokhlin-entropy-action
kind: claim
title: The Gottschalk tester host admits a free ergodic action of positive Rokhlin entropy
distinct_from:
  leavitt-unit-group-has-positive-rokhlin-entropy-action: that asks the entropy question for the binary Leavitt unit group, which would settle Gottschalk's conjecture only for that group; this asks it for the tester host, whose positive answer settles the conjecture for all groups.
  every-group-has-positive-rokhlin-entropy-action: that quantifies over all countably infinite groups; this is the single host, equivalent to it through tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy and the maximality closure on the tester.
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

**OPEN.** The fixed two-generator finitely presented host `U_*` of `gottschalk-surjunctivity-fixed-two-generator-tester` admits a free ergodic p.m.p. action with positive Rokhlin entropy.

By `tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy`, this is equivalent to `bernoulli-rokhlin-entropy-maximal-on-fixed-tester`. It passes down to every infinite countably generated recursively presented group, including the binary Leavitt unit group.

## Attempts

* **Sofic entropy.** `U_*` contains nonsofic groups, and every known lower bound for Rokhlin entropy runs through sofic entropy.
* **Subgroups.** Positive entropy passes down from `U_*` to its infinite subgroups, not up. Restriction bounds the host's Rokhlin entropy only from above.
* **Scope.** The claim is equivalent to Seward's hypothesis that every countably infinite group has a positive-entropy free ergodic action, given the maximality closure recorded on `bernoulli-rokhlin-entropy-maximal-for-every-group`. It is not known to follow from Gottschalk's conjecture.
