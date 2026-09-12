---
rg: 2
id: positive-rokhlin-entropy-on-one-host-proves-gottschalk-proof
kind: route
title: Apply the self-copy dichotomy to a restricted sum of copies of the tester host
target: positive-rokhlin-entropy-on-one-host-proves-gottschalk
requires:
  - rokhlin-supremum-dichotomy-with-centralized-self-copies
  - infinite-rokhlin-supremum-forces-surjunctivity
  - positive-rokhlin-entropy-action-gives-positive-supremum
  - gottschalk-surjunctivity-fixed-two-generator-tester
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

Section 3 of the artifact.

* **Hypotheses.** Splitting the index set into evens and odds embeds `Gamma_U x Gamma_U` in `Gamma_U`, and `S` contains `Sym(n)` for every `n`. So the self-copy corollary of `rokhlin-supremum-dichotomy-with-centralized-self-copies` applies.
* **POS gives INF.** With `positive-rokhlin-entropy-action-gives-positive-supremum`, POS(`Gamma_U`) gives INF(`Gamma_U`).
* **INF gives surjunctivity.** INF(`Gamma_U`) makes `Gamma_U` surjunctive (`infinite-rokhlin-supremum-forces-surjunctivity`).
* **Down to the host.** Surjunctivity passes to subgroups, so `U_*` is surjunctive.
* **All groups.** The tester equivalence of `gottschalk-surjunctivity-fixed-two-generator-tester` then makes every group surjunctive.
* **Kaplansky.** Gottschalk's conjecture implies Kaplansky's direct finiteness conjecture, as Seward records with his reference [8, Section I.5].
