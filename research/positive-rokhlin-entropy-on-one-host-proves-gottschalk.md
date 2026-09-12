---
rg: 2
id: positive-rokhlin-entropy-on-one-host-proves-gottschalk
kind: claim
title: Positive Rokhlin entropy for the fixed tester host implies Gottschalk's conjecture
distinct_from:
  gottschalk-surjunctivity-fixed-two-generator-tester: that reduces Gottschalk's conjecture to surjunctivity of one finitely presented host; this reduces it to existence of one positive-entropy free ergodic action of that same host.
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

Let `U_*` be the fixed two-generator finitely presented host of `gottschalk-surjunctivity-fixed-two-generator-tester`. If `U_*` admits a free ergodic p.m.p. action with positive Rokhlin entropy, then every group is surjunctive, so Gottschalk's conjecture holds. Kaplansky's direct finiteness conjecture then holds for all groups and fields.

Seward's Corollary 7.8 (arXiv:1501.03367v4) draws the same conclusion from positive entropy for every countably infinite group. Here one finitely presented group suffices. The reason is `tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy`: `U_*` contains its own square and cyclic groups of every order, so positive entropy on it is all or nothing.

The first version of this claim used the restricted sum `Gamma_U = ⊕_N (U_* x Sym_fin(N))`. That group embeds in `U_*` and gives the same condition (artifact, Remark 3.4).
