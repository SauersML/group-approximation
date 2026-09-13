---
rg: 2
id: unique-games-conjecture
kind: claim
title: For every eps > 0 there is an alphabet size making it NP-hard to tell unique games of value >= 1-eps from value <= eps
root: true
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**OPEN.**  Khot's Unique Games Conjecture: for every `eps > 0` there is an
alphabet size `K = K(eps)` such that, given a two-prover one-round game
whose every constraint is a permutation of a `K`-letter alphabet, it is
NP-hard to distinguish

```text
val(G) >= 1 - eps     from     val(G) <= eps.
```

The gap is *near-1 versus near-0*.  What is known unconditionally is the
2-to-2 Games Theorem, which reaches completeness near `1/2` with
arbitrarily small soundness; the near-1 side is exactly what is missing.

This is a **root** of the graph in its own right, not a lane under the
program goal `non-hyperlinear-group`.  It was opened 2026-08-24 by a user
directive to wire in an external attack on the conjecture, and it shares
vocabulary but no derivation with the repository's operator-algebraic
games region.  The one place the two regions touch is
`perfect-commuting-unique-game-is-classically-satisfiable`, which says a
*perfect* commuting-operator strategy for a unique game already yields a
perfect classical labeling; that rigidity is the mechanism behind
`unique-constraints-orient-at-most-half-of-a-fiber` below, and it is why no
quantum relaxation of the unique-constraint alphabet evades the wall.

The live decomposition here goes through
`rich-2to1-games-conjecture`, which is *equivalent* to this claim by
Braverman--Khot--Minzer, and from there to a single analytic hole,
`affine-orientation-glue-lemma`.

## Attempts

* **Structured 2-to-1 instances.**  Attack the equivalent Rich 2-to-1
  formulation on the `F_lin` instances whose fibers are affine pairs
  `{x, x+b}` -- the instances the presently known hardness machinery
  already produces.  Reduces the problem to producing *richness*, i.e. to
  an alphabet-independent list-decoding step.  This is the live route
  (`ugc-from-rich-2to1-via-bkm-equivalence`).
* **Naive influence transfer.**  Hope that a coordinate with large
  influence after restriction to an affine-pair subcube has large ambient
  influence, so that the ambient influential coordinates form the bounded
  label list.  **Dead**: `linear-pairing-memorizer-restricts-to-a-dictator`
  exhibits a bounded, low-degree, noise-invariant function that is an exact
  dictator on the quotient while every ambient influence tends to 0.
* **Manufacturing richness by randomizing constraints.**  **Dead**:
  `edge-conjugation-of-2to1-constraints-is-pure-gauge`.
* **Padding the alphabet with random dummy labels.**  **Dead**:
  `dummy-padding-cannot-beat-the-random-guessing-floor` -- an alphabet-sized
  decoding list only reproduces the game's own random-assignment value.
* **Refuting the conjecture** (an algorithm closing the gap) is not
  represented here; a refutation would land as an established negation
  claim, not as a route.
