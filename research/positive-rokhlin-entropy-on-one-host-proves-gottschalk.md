---
rg: 2
id: positive-rokhlin-entropy-on-one-host-proves-gottschalk
kind: claim
title: Positive Rokhlin entropy for one explicit countable group implies Gottschalk's conjecture
distinct_from:
  gottschalk-surjunctivity-fixed-two-generator-tester: that reduces Gottschalk's conjecture to surjunctivity of one finitely presented host; this reduces it to existence of a positive-entropy free ergodic action of one countable group containing that host.
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

Let `U_*` be the fixed two-generator host of `gottschalk-surjunctivity-fixed-two-generator-tester`, and let `S = Sym_fin(N)` be the finitary symmetric group. Put

```text
Gamma_U = restricted direct sum over i in N of (U_* x S).
```

If `Gamma_U` admits a free ergodic p.m.p. action with positive Rokhlin entropy, then every group is surjunctive, so Gottschalk's conjecture holds. Kaplansky's direct finiteness conjecture then holds for all groups and fields.

Seward's Corollary 7.8 (arXiv:1501.03367v4) draws the same conclusion from positive entropy for every countably infinite group. Here one explicit group suffices.

`Gamma_U` is not finitely generated. Any countable group that contains `U_*`, contains its own square, and has finite subgroups of unbounded order works equally well.
