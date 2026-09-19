---
rg: 2
id: tail-child-surplus-collision-proof
kind: route
title: Bound the child-to-next support leakage and apply the Schur surplus recurrence
target: tail-wordized-child-surplus-collision-supplies-rct7
requires:
  - recursive-clifford-tail-supplies-anchor-but-not-contraction
  - schur-violation-density-gives-contraction
  - unitary-offdiagonal-block-gram-is-support-leakage
  - contractive-computation-ladder
---

The overlap in `(TSC5)` is at most `tr(Q_(n+1))`, proving the child-to-next
rank bound.  Substitute the robust violation floor `(TSC2)` and child surplus
identity `(TSC3)` to obtain `(TSC6)`.

Equation `(TSC10)` is direct multiplication by the two carrier reflections;
unitary invariance gives `(TSC9)`.  Polynomial word telescoping yields
`(TSC11)`, after which `contractive-computation-ladder` proves the energy
floor.

For completeness, zero forbidden mass makes the two carrier multiplicities
equal.  Infinite amplification supplies their conjugator, and the HNN
extension embeds the base by Britton's lemma.  This proves every asserted
clause.
