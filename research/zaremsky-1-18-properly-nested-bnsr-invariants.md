---
rg: 2
id: zaremsky-1-18-properly-nested-bnsr-invariants
kind: claim
title: "Zaremsky Problem 1.18 resolved: is there a group of type F_infinity whose BNSR invariants are properly nested in every degree?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 18, verbatim:
"Does there exist a group G of type F∞ such that the BNSR-invariants
Σ1(G) ⊋ Σ2(G) ⊋ · · · are all properly nested?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-18-by-yes` requires
  `f-infinity-group-with-properly-nested-bnsr-invariants`.
- **No**: `zaremsky-1-18-by-no` requires
  `every-f-infinity-group-has-a-non-proper-bnsr-inclusion`.

Never write a `requires: []` route into this claim.

**Reading.** `S(G) = (Hom(G,R) \ {0}) / R_{>0}` is the character sphere, and
`Σ^m(G) ⊆ S(G)` is the homotopical Bieri–Neumann–Strebel–Renz invariant,
defined when `G` is of type `F_m`. Always `Σ^1(G) ⊇ Σ^2(G) ⊇ ⋯`. The question
asks for one group `G` of type `F_∞` with `Σ^m(G) ≠ Σ^{m+1}(G)` for every
`m ≥ 1`. Its negation is that every group of type `F_∞` has at least one
equality `Σ^m(G) = Σ^{m+1}(G)`. That is weaker than eventual constancy, since
a chain may pause and then drop again. A variant with the homological
invariants `Σ^m(G;Z)` is also natural; this root is about the homotopical
invariants, the ones Zaremsky's papers call BNSR invariants.

**What the problem statement already rules out.** The chain must carry
infinitely many distinct compact sets `S(G) \ Σ^m(G)` inside a sphere of fixed
finite dimension `rank(G^{ab}) − 1`. Finite products give long finite chains:
for `G = F_2^n` a character nonzero on exactly `j` factors lies in
`Σ^{j−1} \ Σ^j`, so `S ⊋ Σ^1 ⊋ ⋯ ⊋ Σ^n = ∅`, and then the chain is constant.
An affirmative answer cannot be of type F
(`type-f-bnsr-invariants-stabilize-at-dimension`) and cannot have the Bieri
Σ-property (`bieri-sigma-property-forces-bnsr-constant-from-rank`). Both are
established. Every computed infinite-dimensional `F_∞` example stops at level
2: Thompson's `F`, `F_{n,∞}`, the Stein group `F_{2,3}`, the Lodha–Moore
groups. The negative answer reduces, by an exhaustive split, to
`non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion`.

## Attempts

- 2026-09-13 (lane z1-18-nested-bnsr): region opened. Routes of attack and the
  mechanism analysis are in the two answer claims. Status check not yet done:
  web search was unavailable to this lane, and an arXiv listing sweep is
  running on MSI.
