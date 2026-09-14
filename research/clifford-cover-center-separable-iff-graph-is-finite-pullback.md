---
rg: 2
id: clifford-cover-center-separable-iff-graph-is-finite-pullback
kind: claim
title: The central involution of a Clifford cover survives a finite quotient exactly when the graph is a finite pullback
distinct_from:
  complete-graph-clifford-cover-center-dies-in-finite-quotients: that shows the center dies in every finite quotient for the complete graph; this characterizes, for every invariant graph, when it survives in some finite quotient.
  separated-finite-normal-subgroups-preserve-surjunctivity: that is the surjunctivity theorem for finite normal subgroups injecting into a finite quotient; this decides exactly which Clifford covers satisfy its hypothesis.
  invariant-graph-clifford-phase: that computes the image of the Kun--Thom marked word in the Clifford covers and their tracial models; this is about finite quotients of the covers and says nothing about the marked word.
artifacts:
  - research/artifacts/clifford-cover-orbital-localization-2026-09-12.md
---

Let `G` be a group, `X` a `G`-set with finitely many orbits, `S` a `G`-invariant graph on `X`, and
`E_S = Vtilde_S semidirect G` the Clifford cover with central involution `eps`, as in
`kun-thom-clifford-cover-weakly-sofic`. Then `eps` survives in some finite quotient of `E_S` if and only if
`S` is a **finite pullback**: for some finite-index normal `K` of `G`, `S` is pulled back from a
`G`-invariant graph on the finite set `K\X`, and no edge joins two sites of one `K`-fibre.

**ESTABLISHED** by `clifford-cover-center-separable-pullback-proof` (artifact Section 1, Theorem A).

**Consequences.**
- If `G` is surjunctive and `S` is a finite pullback, `E_S` is surjunctive, by
  `separated-finite-normal-subgroups-preserve-surjunctivity` and
  `rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`.
- For `X = G/Gamma` with `Gamma` of infinite index, no finite-degree graph with an edge is a finite
  pullback, and neither is the complete graph. For the Kun--Thom pair, every finite-degree Clifford cover and
  the complete-graph cover lie in the open residue of `finite-normal-subgroups-do-not-affect-surjunctivity`.
