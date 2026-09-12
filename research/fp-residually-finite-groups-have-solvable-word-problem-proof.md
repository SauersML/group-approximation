---
rg: 2
id: fp-residually-finite-groups-have-solvable-word-problem-proof
kind: route
title: Run the consequence enumeration against an enumeration of finite permutation quotients
target: fp-residually-finite-groups-have-solvable-word-problem
requires: []
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

Let `w` be a word in `X^{±1}`. Run two procedures in parallel.

1. Enumerate all products of conjugates of relators and free reductions.
   If `w = 1` in `G`, some such derivation reaches `w`, so this halts.
2. For `n = 1, 2, ...` enumerate all maps `f: X -> Sym(n)`. There are
   finitely many for each `n`, and one checks the finitely many relators of
   `R` on each. A map killing every relator is a homomorphism `G -> Sym(n)`.
   Halt with "nontrivial" if some such homomorphism has `f(w) != 1`.

If `w != 1`, residual finiteness gives a finite quotient `q: G -> Q` with
`q(w) != 1`; left multiplication embeds `Q` in `Sym(|Q|)`, so procedure 2
halts. If `w = 1`, no homomorphism detects it, so procedure 2 never gives a
wrong answer. Exactly one of the two halts. Finite presentation is used in
both halves: in (1) to enumerate the consequences and in (2) to recognize
homomorphisms by finitely many checks. `∎`
