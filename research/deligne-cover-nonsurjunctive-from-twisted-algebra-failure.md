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

*Verification by `w4-vf-linear-b` (2026-09-12), Section 27 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication.*
- *The padding goes through the central idempotents of `<z>`, which needs `w ∈ F` and `p != 3`.*
- *The automaton lemma needs a finite `F`. A witness over any field of characteristic `p` descends to a finite field: the entries generate a finitely generated `F_p`-domain, and a nonzero entry of `AB - I` survives modulo some maximal ideal with finite residue field.*
