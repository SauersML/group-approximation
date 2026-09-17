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

Full uniformity is more than the reduction needs.
`noise-test-sound-on-smooth-design-rich-inputs` shows the published soundness
proof uses only a strength-`(8d+1)` pairing design with the pull-back density
comparison. That weaker hypothesis is `smooth-design-rich-2to1-hardness`, which
feeds UGC through `ugc-from-smooth-design-rich-2to1`.

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
* **Prove soundness by an operator-algebraic (entanglement-robust) analysis.**
  Examples: matrix-valued hypercontractivity, quantum rigidity or low-degree
  tests as the soundness engine, or an inner decoder that handles entangled
  strategies. **Attempted, held OPEN (2026-09-17):** the kill below was drafted but
  referees refuted it as written. Lens 1: B3 omits the outer completeness and
  polynomial-time hypotheses on `O` that its proof uses. Lens 2: KRT Theorems 1.3
  and 4.5 apply to unique games only, so an entanglement-sound outer PCP to rich
  2-to-1 games followed by the classically sound noise test is not killed; the
  kill can at most cover soundness conclusions about the output unique game.
  The drafted content:
  - `entanglement-sound-soundness-cannot-prove-ugc` (via the Kempe--Regev--Toner
    import `unique-games-entangled-value-approximable-by-sdp`) shows such an
    analysis puts the source language in P when `6 eps + delta < 1`.
  - Under P != NP, every NP-hardness reduction to Gap-UG must produce infinitely
    many NO instances of entangled value `>= 1 - 6 eps`.
  - Composition with a classically sound outer PCP and an entangled-strategy
    decoder `D_cl`, or with an entanglement-sound outer PCP and a decoder `D_q`,
    also dies.
  - Unconditionally, for the binary test,
    `clifford-long-codes-realize-pairing-value-in-binary-noise-test`
    gives fully rich 2-to-1 games of value `<= 4/k^eta` whose `R_(rho,2)` output
    has entangled value `>= (1 + rho^3 (1 - 9 eta)^2)/2`.

  (Drafted conclusion, not established: a proof of this conjecture whose soundness
  conclusion is about the output unique game must use a step that is false for
  entangled strategies.) Open: an explicit clock-and-shift witness for `m > 2`.
