---
rg: 2
id: zaremsky-1-21-g-times-z-type-f-implies-g-type-f
kind: claim
title: "Zaremsky Problem 1.21 resolved: if G x Z is of type F, must G be of type F?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 21, verbatim:
"(Added 7/24/25) For a group G, if G × Z is of type F then is G of type F? This
turns out to be equivalent to: If G is of type F∞ and has finite cohomological
dimension then is G of type F?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-21-by-yes` requires
  `f-infinity-groups-of-finite-cd-are-of-type-f` and
  `g-times-z-type-f-iff-g-f-infinity-with-finite-cd`.
- **No**: `zaremsky-1-21-by-no` requires
  `some-f-infinity-group-of-finite-cd-is-not-of-type-f` and
  `g-times-z-type-f-iff-g-f-infinity-with-finite-cd`.

Never write a `requires: []` route into this claim.

**Reading.** Type F: a finite CW complex `K(G,1)`. Type `F_∞`: a `K(G,1)` with
finite skeleta. `cd` is cohomological dimension over `Z`. `G × Z` is the direct
product with the infinite cyclic group. Nothing else is hidden in the statement.

**Equivalent forms, established in this graph.**

1. `g-times-z-type-f-iff-g-f-infinity-with-finite-cd`: for every group `G`,
   `G × Z` is of type F iff `G` is of type `F_∞` with finite `cd` iff `G` is
   finitely presented and of type FP. This proves the equivalence the list
   states.
2. `fp-type-fp-group-is-type-f-iff-wall-class-vanishes`: a finitely presented
   group of type FP is of type F iff it is of type FL iff its Wall class
   `σ(G) = Σ (−1)^i [P_i] ∈ K̃_0(ZG)` vanishes, for any finite projective
   resolution `P_* → Z`.

So the question asks whether `σ(G) = 0` for every finitely presented group of
type FP, that is, whether "finitely presented and FP" implies FL. By Wall's
characterization of finitely dominated complexes (C. T. C. Wall, Finiteness
conditions for CW-complexes, Ann. of Math. 81 (1965)) this is the same as
asking whether every finitely dominated aspherical CW complex is homotopy
equivalent to a finite complex.

**Status and expected answer.** Open per the list. `σ(G) = 0` whenever
`K̃_0(ZG) = 0` (`f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f`),
and the K-theoretic Farrell–Jones conjecture predicts `K̃_0(ZG) = 0` for every
torsion-free group. Groups of type FP have finite `cd`, so they are torsion-free.
A negative answer is therefore a torsion-free finitely presented group of type
FP with `K̃_0(ZG) ≠ 0`, which would also refute the Farrell–Jones conjecture in
degree 0 with integer coefficients.

**Neighbours on the list.** Problem 4.6 (`zaremsky-4-06-f-infinity-finite-cd-contractible-rips`):
a contractible Rips complex for every `F_∞` group of finite `cd` gives "yes"
here, as the list says; a "no" here gives "no" there. Problem 4.7 is adjacent.

## Attempts

- 2026-09-13 (lane z1-21-wall-obstruction): reduced to vanishing of the Wall
  class and firewalled a counterexample through `K̃_0(ZG)`; constructive attempts
  toward a counterexample are recorded on
  `some-f-infinity-group-of-finite-cd-is-not-of-type-f`, affirmative attempts on
  `f-infinity-groups-of-finite-cd-are-of-type-f`.
