---
rg: 2
id: fpbs-sheet-spines-not-weakly-contained-in-bernoulli
kind: claim
title: An invariant spine made of whole sheets over a nontrivial random height set is not weakly contained in Bernoulli, and is not strongly ergodic when the height law is atomless
distinct_from:
  fpbs-fiid-soft-collapse-iff-fiid-sparse-spines: that is the FIID soft-collapse theorem with Corollaries D and E; this is only the corrected second bullet of its Proposition F, split out after a referee refuted the unrestricted "not strongly ergodic" version
  fpbs-soft-collapse-iff-invariant-sparse-spines: that builds the invariant sheet spines (Theorem B); this says what those spines are not
---

**OPEN** (split out 2026-09-17 as the refuted step of
`fpbs-fiid-soft-collapse-iff-fiid-sparse-spines-proof`, after referee lens 1
refuted the unrestricted second bullet of Proposition F in the atomic case).

Let `Gamma` be finitely generated and nonamenable, `pi: Gamma -> Z` onto, and
`L` an invariant random subgraph of a Cayley graph of `Gamma` such that
`Ĥ = {h : pi^-1(h) ⊆ V(L)}` is a.s. neither `∅` nor `Z`. Then the process `L`
is not weakly contained in the Bernoulli shift of `Gamma`. If moreover the
law of `Ĥ` is atomless, the process is not strongly ergodic.

## Attempts

* **The argument in `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines-proof`
  ("Second bullet").** Weak containment in Bernoulli forces ergodicity. In the
  atomic case a finite orbit of period `r >= 2` gives a nontrivial invariant
  set for `pi^-1(rZ)`, whose Bernoulli restriction is strongly ergodic, so
  weak containment fails. In the atomless case the Rokhlin lemma gives
  almost-invariant sets under bounded translations.
  **Referee status (2026-09-17):** lens 1 found the non-weak-containment
  conclusion sound in both cases and the strong-ergodicity conclusion false in
  the atomic case (counterexample: sheets over `rZ + j`, `j` uniform, with iid
  connectors, which is strongly ergodic). The statement above is restricted
  accordingly and awaits a fresh referee pass.
