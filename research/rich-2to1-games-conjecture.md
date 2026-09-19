---
rg: 2
id: rich-2to1-games-conjecture
kind: claim
title: Rich 2-to-1 games are NP-hard to approximate between near-perfect and near-zero value
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**OPEN.**  The Rich 2-to-1 Games Conjecture of Braverman, Khot and Minzer:
the near-1 versus near-0 hardness gap holds for 2-to-1 games carrying the
additional *richness* condition on the constraint structure.

By `rich-2to1-conjecture-is-equivalent-to-ugc` this is not a weakening of
`unique-games-conjecture` but an exact reformulation of it.  Its interest is
that it is stated on instances of the shape the existing 2-to-1 machinery
already builds, so the whole difficulty is concentrated in supplying
richness rather than in redesigning the reduction.

Concretely, write `Omega = F_2^k` and, for `b != 0`, let the fibers be the
affine pairs `{x, x+b}`.  These `F_lin` instances are exactly the structured
distributions the known hardness constructions produce.  The gap between
what those constructions give and what richness demands is an
**alphabet-independent list-decoding step**: the soundness decoder must
return a bounded list of candidate labels, with the bound independent of
the alphabet size.

`dummy-padding-cannot-beat-the-random-guessing-floor` is the exact reason
the independence is not negotiable.

## Attempts

* **Glue the affine orientations analytically.**  Prove
  `affine-orientation-glue-lemma`, which delivers precisely the bounded
  candidate list, and then a hardness endgame.  Live, and the endgame step
  is itself parked as the open implication
  `glue-lemma-implies-rich-2to1-hardness` rather than asserted.
* **Randomize the fibers by conjugating each constraint.**  **Dead** --
  `edge-conjugation-of-2to1-constraints-is-pure-gauge` shows the folded
  long-code restriction is literally unchanged, so no randomness reaches
  the analytic object the test sees.
* **Orient each 2-to-1 fiber with local unique-constraint gadgets.**
  **Dead** -- `unique-constraints-orient-at-most-half-of-a-fiber`.
* **Hide a hard core inside a large randomly matched dummy alphabet.**
  **Dead** -- `dummy-padding-cannot-beat-the-random-guessing-floor`.
