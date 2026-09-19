---
rg: 2
id: stw99-problem-xiv-finite-ssa-quasidiagonal
kind: claim
title: Every finite strongly self-absorbing C*-algebra is quasidiagonal (STW Problem XIV, part 1)
root: true
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that asks whether R itself is quasidiagonal; this asks it for finite strongly self-absorbing C*-algebras, which embed unitally into R, so it is a consequence of that problem (route stw99-x2-implies-xiv1) but could hold independently, e.g. through the UCT.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

**Problem XIV(1) of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Winter, Abel Proceedings 3.9).  If a strongly self-absorbing C\*-algebra
`D` is finite, must it be quasidiagonal?  Equivalently (McDuff-type
characterisation, STW's footnote): is `Q ≅ Q ⊗ D` for the universal UHF
algebra `Q`?

Strongly self-absorbing algebras are automatically simple, nuclear, and
unital with at most one trace; finite ones have a unique faithful trace
and are stably finite.  With the UCT the answer is yes by
Tikuisis--White--Winter, so this problem is exactly the UCT-free residue,
and a positive answer to Problem XIII (UCT for strongly self-absorbing
algebras) closes it.

Upstream routes: `stw99-x2-implies-xiv1` (via R), `stw99-vii-implies-xiv1`
(special case of Blackadar--Kirchberg, as STW note via Kirchberg's
dichotomy), and `stw99-xiv2-implies-xiv1` (Schafhauser 2024: part 2
implies part 1).

## Attempts

* **Via the hyperfinite factor.**  `D` finite strongly self-absorbing has
  a unique faithful trace whose GNS closure is an injective II₁ factor,
  i.e. `R`; so `D` embeds unitally and trace-preservingly into `R`, and a
  positive answer to Problem X(2) implies this problem
  (`stw99-x2-implies-xiv1`).  The session's X(2) lane is therefore
  directly upstream: every obstruction found there (no known
  non-quasidiagonal subalgebra of `R`) is consistent with a positive
  answer here.
* **Conversely** a finite strongly self-absorbing `D` that failed
  quasidiagonality would refute X(2) with an algebra of maximal internal
  symmetry (`D ≅ D^{⊗∞}`), evading all the group-based obstructions of
  the X(2) lane; no candidate is known — every known finite strongly
  self-absorbing algebra (`Z`, UHF of infinite type, and their tensor
  products) satisfies the UCT and is quasidiagonal.
