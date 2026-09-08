---
rg: 2
id: unique-games-conjecture
kind: claim
title: For every eps > 0 there is an alphabet size making it NP-hard to tell unique games of value >= 1-eps from value <= eps
root: true
goal: true
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
  - research/artifacts/approximation-cs-root-audit-2026-08-31.md
  - research/artifacts/unique-games-noisy-direction-counterexample-2026-09-07.md
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
---

**OPEN.** Khot's Unique Games Conjecture: for every `0 < eps < 1/2` there is an
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

The live equivalence route here goes through
`rich-2to1-games-conjecture`, which is *equivalent* to this claim by
Braverman--Khot--Minzer. The proposed `F_lin` attack was closed on
2026-09-07: `noisy-affine-selector-defeats-bounded-hitting` refutes both
`affine-orientation-glue-lemma` and its proposed star-density input.
The conditional globalization theorem remains valid. A new analytic
formulation and an explicit hardness reduction are needed; the prior
two-hole plan is no longer usable. Neither UGC nor Rich 2-to-1 hardness
is proved or refuted by that counterexample.

## Attempts

* **Direct affine soundness of the published folded noise test.**
  `affine-long-code-test-has-no-uniform-soundness` supplies an explicit
  source family with vanishing value and folded output labelings with
  high acceptance. The complete proof includes all three noise layers,
  a finite-field incidence bound, and the conversion to permutation
  constraints. It closes this test under only `F_lin` richness; it is
  neither a UGC proof nor a UGC counterexample.
* **Structured 2-to-1 instances.**  Attack the equivalent Rich 2-to-1
  formulation on the `F_lin` instances whose fibers are affine pairs
  `{x, x+b}` -- the instances the presently known hardness machinery
  already produces. The published equivalence remains a live route
  (`ugc-from-rich-2to1-via-bkm-equivalence`), but the repository's proposed
  alphabet-independent list lemma is false. Richness is a distributional
  condition on pairings, not a synonym for that lemma.
* **Noisy direction decoding.** A complete counterexample to the proposed
  analytic bridge is recorded in
  `noisy-affine-selector-defeats-bounded-hitting`, with exact finite replay.
  The adversarial function is Boolean and folded and survives every fixed
  positive noise parameter. Those conditions alone cannot repair the bridge.
* **Naive influence transfer.**  Hope that a coordinate with large
  influence after restriction to an affine-pair subcube has large ambient
  influence, so that the ambient influential coordinates form the bounded
  label list.  **Dead**: `linear-pairing-memorizer-restricts-to-a-dictator`
  exhibits a bounded homogeneous function whose noisy restriction stays a
  fixed multiple of a dictator while every ambient influence tends to 0.
* **Manufacturing richness by randomizing constraints.**  **Dead**:
  `edge-conjugation-of-2to1-constraints-is-pure-gauge`.
* **Padding the alphabet with random dummy labels.**  **Dead**:
  `dummy-padding-cannot-beat-the-random-guessing-floor` -- an alphabet-sized
  decoding list only reproduces the game's own random-assignment value.
* **Refuting the conjecture** (an algorithm closing the gap) is not
  represented here; a refutation would land as an established negation
  claim, not as a route.
