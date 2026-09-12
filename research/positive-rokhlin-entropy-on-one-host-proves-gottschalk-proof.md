---
rg: 2
id: positive-rokhlin-entropy-on-one-host-proves-gottschalk-proof
kind: route
title: Apply the self-copy dichotomy to the tester host itself and use the tester equivalence
target: positive-rokhlin-entropy-on-one-host-proves-gottschalk
requires:
  - tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy
  - infinite-rokhlin-supremum-forces-surjunctivity
  - gottschalk-surjunctivity-fixed-two-generator-tester
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Section 3 of the artifact.

* **All or nothing.** By `tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy`, POS(`U_*`) gives INF(`U_*`).
* **INF gives surjunctivity.** `infinite-rokhlin-supremum-forces-surjunctivity` makes `U_*` surjunctive.
* **All groups.** The tester equivalence of `gottschalk-surjunctivity-fixed-two-generator-tester` then makes every group surjunctive.
* **Kaplansky.** Gottschalk's conjecture implies Kaplansky's direct finiteness conjecture, as Seward records with his reference [8, Section I.5] (Capraro–Lupini).

gk-verify-pos independently re-derived the restricted-sum version on 2026-09-12: PASS (Section 13 of the verification artifact). reviewer-2 also passed it (`review-rokhlin-self-copy-dichotomy-2026-09-12.md`). The finitely presented version replaces the evens-and-odds square by the container embedding of `U_* x U_*`.
