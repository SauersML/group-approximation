---
rg: 2
id: rich-2to1-games-conjecture
kind: claim
title: Rich 2-to-1 games are NP-hard to approximate between near-perfect and near-zero value
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
  - research/artifacts/unique-games-noisy-direction-counterexample-2026-09-07.md
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
---

**OPEN.**  The Rich 2-to-1 Games Conjecture of Braverman, Khot and Minzer:
the near-1 versus near-0 hardness gap holds for 2-to-1 games carrying the
additional *richness* condition: at each left vertex, a uniformly sampled
incident edge induces a uniformly random perfect pairing of the left
alphabet. This is Definition 5 of the cited ITCS paper.

By `rich-2to1-conjecture-is-equivalent-to-ugc` this is not a weakening of
`unique-games-conjecture` but an exact reformulation of it.  Its interest is
that it is stated on instances of the shape the existing 2-to-1 machinery
already builds, so the whole difficulty is concentrated in supplying
richness rather than in redesigning the reduction.

The known `F_lin` family pairs `x` with `x+b` on `F_2^k` for a uniform
nonzero `b`. It is much smaller than the family of all perfect pairings.
The proposed alphabet-independent list-decoding lemma for this family was
refuted on 2026-09-07 by `noisy-affine-selector-defeats-bounded-hitting`.
Consequently that proposed bridge does not supply the missing richness.

`dummy-padding-cannot-beat-the-random-guessing-floor` explains why an
alphabet-sized decoding list cannot supply the intended soundness gain.

## Attempts

* **Use the folded long-code noise test with only affine richness.**
  **Dead as a uniform soundness argument:**
  `affine-long-code-test-has-no-uniform-soundness` gives explicit source
  games of value at most `2/sqrt(N)` whose transformed games have value
  close to one. The published result's full-richness hypothesis is not
  supplied by the affine direction distribution. This leaves open tests
  or input families with additional structure.
* **Stop at an intermediate algebraic family.** **Dead for the noise test:**
  `separated-small-pairing-families-defeat-the-noise-test` extends the affine
  obstruction to every separated pairing family of subexponential size, e.g.
  affine or bounded-degree polynomial involutions. Route
  `ugc-via-subexponential-pairing-enrichment` records the kill. The pairing
  distribution at a left vertex must carry entropy linear in the alphabet size
  before this test applies.
* **Glue the affine orientations analytically.** **Dead:**
  `affine-orientation-glue-lemma` is refuted, and its conditional hardness
  route is invalidated. The historical endgame proposal
  `glue-lemma-implies-rich-2to1-hardness` never supplied an explicit reduction.
* **Randomize the fibers by conjugating each constraint.**  **Dead** --
  `edge-conjugation-of-2to1-constraints-is-pure-gauge` shows the folded
  long-code restriction is literally unchanged, so no randomness reaches
  the analytic object the test sees.
* **Orient each 2-to-1 fiber with local unique-constraint gadgets.**
  **Dead** -- `unique-constraints-orient-at-most-half-of-a-fiber`.
* **Hide a hard core inside a large randomly matched dummy alphabet.**
  **Dead** -- `dummy-padding-cannot-beat-the-random-guessing-floor`.
