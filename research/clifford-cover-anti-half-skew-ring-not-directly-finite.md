---
rg: 2
id: clifford-cover-anti-half-skew-ring-not-directly-finite
kind: claim
title: The anti-central Clifford skew group ring of some Kun--Thom Clifford cover is not directly finite
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is a corner problem in the anti-central summand of the ternary Leavitt unit group algebra; this is direct finiteness of a skew group ring over a Clifford-type lamp algebra with a compressing coset action.
  kun-thom-wreath-stably-finite: that is stable finiteness of the untwisted wreath group algebras; this is the twisted anti-central factor, which that theorem does not cover.
artifacts:
  - research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md
---

**OPEN.** For the Kun--Thom Theorem E pair and some `G`-invariant graph `S` on `X = G/Gamma`, the skew
group ring `A_S` of `clifford-cover-group-algebra-splits-into-wreath-and-skew-ring` contains
`a, b` with `b a = 1 != a b`.

## Attempts

- **Why it is not already excluded.** The landed linear theorem
  `rf-lamps-preserve-stable-finiteness-for-arbitrary-actions` inducts through site projections onto
  matrix algebras over stabilizer group algebras.
  - For the complete graph the lamp algebra is the infinite Clifford algebra over `F_3`. It is a directed
    union of central simple algebras `M_(2^k)(F_3)`, hence simple and infinite-dimensional.
  - So it has no algebra maps onto finite site pieces, and the induction has nothing to project to.
- **Obstructions still standing.** The normalized trace of the Clifford algebra is `G`-invariant, which
  gives an `F_3`-valued trace on `A_S`. A defect must have trace `0` mod 3. This constrains but does not
  forbid.
- **Where a construction must get its room.**
  - Compression `u Gamma u^-1 < Gamma` gives an equivariant non-injective self-map of `X`. Its fibers have
    size `[Gamma : u Gamma u^-1]`, which is infinite for the Theorem E pair, so no finite lamp product
    implements it.
  - A witness needs a mechanism other than a finite-fiber site map, for example isometry-like elements
    built from lamp unitaries along the orbit structure of `u`.
