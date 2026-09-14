---
rg: 2
id: deligne-cover-nonsurjunctive-from-twisted-algebra-failure
kind: route
title: A one-sided inverse over a Deligne-twisted group algebra of Sp4(Z) refutes surjunctivity of the triple cover
target: deligne-triple-cover-nonsurjunctive
requires:
  - deligne-twisted-group-algebra-is-not-stably-finite
  - stable-finiteness-failure-refutes-surjunctivity
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
---

For `p != 3`, `F[E_3] = F[Sp_4(Z)] x A_1 x A_2` by the central idempotents of `<z>` (w3-deligne artifact,
Lemma 4.1).
1. A pair `BA = 1 != AB` in `M_n(A_j)`, padded by the units of the other two factors, is a one-sided pair in
   `M_n(F[E_3])`.
2. `stable-finiteness-failure-refutes-surjunctivity` turns it into an injective non-surjective linear
   automaton on `(F^n)^(E_3)`.
