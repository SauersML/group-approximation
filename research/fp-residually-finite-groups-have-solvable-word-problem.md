---
rg: 2
id: fp-residually-finite-groups-have-solvable-word-problem
kind: claim
title: Finitely presented residually finite groups have solvable word problem
distinct_from:
  simple-envelope-forces-solvable-word-problem: that derives decidability from finite presentation plus simplicity of an ambient group; this derives it from finite presentation plus residual finiteness of the group itself, and the nontriviality search runs through finite quotients instead of through collapse.
  clapham-fp-embedding-preserves-word-problem: that is an embedding theorem preserving decidability; this is the classical decidability theorem for one class of finitely presented groups and embeds nothing.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**ESTABLISHED.** If `G = <X | R>` with `X, R` finite and `G` residually
finite, then `G` has solvable word problem (McKinsey 1943, Mal'cev 1958).

So every finitely presented residually finite group is an input of
`boone-higman-conjecture`, and the residually finite subproblem
`fp-residually-finite-boone-higman` is a special case of it.

DERIVATION
fp-residually-finite-groups-have-solvable-word-problem-proof
