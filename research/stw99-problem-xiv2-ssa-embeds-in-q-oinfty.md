---
rg: 2
id: stw99-problem-xiv2-ssa-embeds-in-q-oinfty
kind: claim
title: Every strongly self-absorbing C*-algebra other than O_2 embeds into the ultrapower of Q tensor O-infinity (STW Problem XIV, part 2)
root: true
distinct_from:
  stw99-problem-xiv-finite-ssa-quasidiagonal: that is the finite case, quasidiagonality of finite strongly self-absorbing algebras; this is Kirchberg's general conjecture (Abel Conjecture 4.7) that every strongly self-absorbing D other than O_2 embeds into (Q ⊗ O_∞)_ω, equivalently Q ⊗ O_∞ is D-stable, and it implies the finite case by Schafhauser's recent theorem.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

**Problem XIV(2) of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Kirchberg, Abel Proceedings Conjecture 4.7; Winter 3.10).  If `D` is
strongly self-absorbing and `D ≇ O_2`, does `D` embed into
`(Q ⊗ O_∞)_ω`?  Equivalently, is `Q ⊗ O_∞ ≅ Q ⊗ O_∞ ⊗ D`?

Schafhauser (arXiv 2024, Corollary 4.6) proved that a positive answer here
implies a positive answer to part 1 (`stw99-xiv2-implies-xiv1`).  With the
UCT the answer is known: the strongly self-absorbing algebras are then
exactly `Z`, the infinite-type UHF algebras, `O_∞`, their tensor products,
and `O_2`, and all but `O_2` embed.  So, like part 1, this problem is the
UCT-free residue of the classification of strongly self-absorbing
algebras, and Problems XV and XVI of STW split off the K-theoretic and
uniqueness components.

## Attempts

* The `O_2`-exception is forced: `Q ⊗ O_∞` has nonzero `K_0`, while every
  unital subalgebra... rather, `O_2`-stability would collapse the unit's
  class; `O_2` embeds unitally into everything Kirchberg, but
  `Q ⊗ O_∞ ⊗ O_2 ≅ O_2 ≇ Q ⊗ O_∞` distinguishes the stability form.
* Any counterexample is a strongly self-absorbing algebra outside the
  known list, hence (through classification) a UCT counterexample; no
  candidate construction is known.  Winter's "microcosm" heuristic makes
  this and Problem XIII the concentrated form of the UCT problem
  (Problem II of STW).
