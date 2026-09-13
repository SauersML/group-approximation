---
rg: 2
id: zaremsky-1-13-sigma-infinity-is-open
kind: claim
title: "Zaremsky Problem 1.13 resolved: must the BNSR invariant Sigma^infinity(G) be open?"
root: true
artifacts:
  - research/artifacts/zp-sigma-infinity-openness-2026-09-13-part1.md
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

**Reductions landed with this root (both established).**

- `non-open-sigma-infinity-needs-unbounded-sigma-depth`: `Σ^∞(G)` can fail to
  be open at `χ` only if characters of finite but arbitrarily large depth
  `min{n : ψ ∉ Σ^n(G)}` accumulate at `χ`. So the `Σ^n(G)` must take infinitely
  many distinct values.
- `bnsr-invariants-stabilize-at-cohomological-dimension`: if `cd G = d < ∞` the
  invariants stabilize from index `max(d,2)`. So a counterexample has infinite
  cohomological dimension.

**Known computations.** Every group of type `F_∞` of infinite cohomological
dimension whose invariants have been computed (Thompson's `F`, the generalized
Thompson groups `F_{n,∞}`, the golden-mean group `F_τ`, the Lodha–Moore groups,
the Stein group `F_{2,3}`) has `Σ^m = Σ^2` for all `m ≥ 2`; see the artifact,
§2. A negative answer
needs a group whose BNSR invariants never stabilize, the territory of Problem
1.18 (`zaremsky-1-18-properly-nested-bnsr-invariants`, which asks for every
inclusion to be proper, while 1.13 needs only infinitely many distinct
invariants with a non-open limit).

## Attempts

- 2026-09-13 (lane z1-13-sigma-inf): the two reductions above and a bounded
  literature sweep (artifact §2): no known group has non-open `Σ^∞`, and none of
  type `F_∞` is known to have infinitely many distinct invariants. Mechanisms
  for a "no" answer and their status are in artifact §3: products never help
  (depth is additive), two-ended Thompson-like groups saturate at `m = 2`,
  arithmetic depth and tropical jump loci are consistent with openness of each
  `Σ^m` but unexplored, and pure braided Thompson groups (Problem 2.13) are a
  candidate. Status: open.
