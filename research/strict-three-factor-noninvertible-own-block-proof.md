---
rg: 2
id: strict-three-factor-noninvertible-own-block-proof
kind: route
title: A fully peelable automaton is surjective, so a strict one has a non-peelable own-block row
target: strict-three-factor-needs-noninvertible-own-block
requires:
  - own-block-local-bijection-rows-peel
  - peeling-to-surjunctive-memory-tail-forces-surjectivity
  - central-c3-quadratic-surjunctivity-iff-direct-finiteness
artifacts:
  - research/artifacts/corrected-tail-peeling-boundary-2026-09-12.md
---

Section 3, Theorem 3.1 of the artifact. Suppose, for contradiction, that some
ordering peels every block of the strict injective `F` by type (Z), type (O), or
own-block local-bijection steps. Then by `own-block-local-bijection-rows-peel`
down the chain, `F` is surjective iff the final tail is, and the final tail is
empty (no unknown), hence bijective; so `F` is surjective by
`peeling-to-surjunctive-memory-tail-forces-surjectivity` with the trivial
subgroup. This contradicts strictness. Therefore every ordering halts at a row
whose own-block self-map is not a local bijection. Such a failure is either a
non-invertible own-linear part (B1, containing stable finiteness of `R[G]`) or a
non-invertible own-block nonlinearity; the minimal instance of the latter is the
central three-cycle row, which by
`central-c3-quadratic-surjunctivity-iff-direct-finiteness` is equivalent to
characteristic-two direct finiteness.
