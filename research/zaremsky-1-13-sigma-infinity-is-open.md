---
rg: 2
id: zaremsky-1-13-sigma-infinity-is-open
kind: claim
title: "Zaremsky Problem 1.13 resolved: must the BNSR invariant Sigma^infinity(G) be open?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 13, verbatim:
"Every Σ^n(G) is an open subset of the character sphere Σ(G), but what about
Σ^∞(G)? Must that be open?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-13-by-yes` requires
  `every-f-infinity-group-has-open-sigma-infinity`.
- **No**: `zaremsky-1-13-by-no` requires
  `some-f-infinity-group-has-non-open-sigma-infinity`.

Never write a `requires: []` route into this claim.

**Reading.** `G` is a group of type `F_∞`, so every homotopical BNSR invariant
`Σ^n(G)` is defined. `S(G) = (Hom(G,R) \ {0}) / R_{>0}` is the character sphere
(the list writes `Σ(G)` for it), and `Σ^∞(G) = ∩_{n ≥ 1} Σ^n(G)`. The question
asks whether `Σ^∞(G)` is open in `S(G)` for every such `G`. The homological
variant `Σ^∞(G;Z) = ∩_n Σ^n(G;Z)`, for `G` of type `FP_∞`, is the parallel
question; each answer claim says which invariant it covers.

**Reduction landed with this root.** `Σ^∞(G)` is a countable intersection of
open sets. It can fail to be open at a character `χ ∈ Σ^∞(G)` only if characters
of finite but arbitrarily large "depth" `min{n : ψ ∉ Σ^n(G)}` accumulate at `χ`;
in particular the sets `Σ^n(G)` must take infinitely many distinct values
(`non-open-sigma-infinity-needs-unbounded-sigma-depth`). So a "no" answer
produces a group of type `F_∞` whose BNSR invariants never stabilize, which is
the territory of Problem 1.18 (`zaremsky-1-18-properly-nested-bnsr-invariants`,
a different question: 1.18 asks for every inclusion to be proper, 1.13 only
needs infinitely many distinct invariants with a non-open limit).

## Attempts

- 2026-09-13 (lane z1-13-sigma-inf): depth reduction above (established). Next:
  stabilization for groups with a finite classifying space, a survey of every
  computed `Σ^m` sequence for infinite-dimensional `F_∞` groups (Thompson-like
  groups), and candidate constructions with unbounded depth. Status: open.
