---
rg: 2
id: kun-thom-clifford-cover-nonsurjunctive
kind: claim
title: Some Kun--Thom Clifford cover is not surjunctive
root: true
distinct_from:
  kun-thom-nonsofic-wreaths-are-surjunctive: that proves the Kun--Thom wreath W surjunctive; this asks whether its central Z/2 cover E_S fails surjunctivity.
  finite-normal-subgroups-do-not-affect-surjunctivity: that is the universal closure statement for finite normal subgroups; this would refute it on one explicit central extension.
  leavitt-unit-group-nonsurjunctive: that seeks a counterexample on a simple Leavitt host; this seeks one on a weakly sofic central extension of a surjunctive group.
artifacts:
  - research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md
---

**OPEN.** For the Kun--Thom Theorem E pair and some `G`-invariant graph `S` on `X = G/Gamma`, the Clifford
cover `E_S = Vtilde_S semidirect G` of `kun-thom-clifford-cover-weakly-sofic` carries an injective,
non-surjective cellular automaton over a finite alphabet.

Payoff: `E_S` would refute Gottschalk's conjecture. Its quotient `E_S/<eps> = W` is surjunctive, so it
would also refute `finite-normal-subgroups-do-not-affect-surjunctivity`, on a weakly sofic host.

Marked `root` because it heads a counterexample lane of its own.

## Attempts

- **Permanence cannot reach it.** `kun-thom-clifford-cover-has-no-finitary-site-structure`:
  the finitary split-extension theorem does not apply. For the complete graph,
  `complete-graph-clifford-cover-center-dies-in-finite-quotients`: the separated finite-normal theorem
  does not apply either.
- **Linear case.** `clifford-cover-group-algebra-splits-into-wreath-and-skew-ring` reduces it to direct
  finiteness of the Clifford skew group ring `A_S`
  (`clifford-cover-anti-half-skew-ring-not-directly-finite`).
- **Nonlinear case.** Not attempted yet. Any strict automaton must fold its Garden of Eden on
  sofic-invisible elements, and `eps` is invisible to every finite quotient.
