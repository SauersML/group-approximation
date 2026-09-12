---
rg: 2
id: hyperbolic-group-trivial-radical-residual-prime-torsion
kind: claim
title: A hyperbolic group with trivial finite radical and prime-order torsion in its finite residual
distinct_from:
  non-virtually-torsion-free-hyperbolic-group: that allows the invisible torsion to sit inside a finite normal subgroup; this demands a trivial finite radical, which forces the non-elementary alternative of the prime-torsion dichotomy, and is nonetheless equivalent
  hyperbolic-prime-torsion-residual-dichotomy: that classifies a failure of virtual torsion-freeness into two alternatives; this is the existence claim for the non-elementary alternative, into which every counterexample can be converted
  non-residually-finite-hyperbolic-group: that asks for any failure of residual finiteness; this fixes the most rigid shape a failure can be given, and the two are equivalent
---

Exhibit a word-hyperbolic group `H` whose maximal finite normal subgroup is
trivial and whose finite residual contains an element `x` of prime order.

By `hyperbolic-prime-torsion-residual-dichotomy`, the normal closure of `x` in
such an `H` is non-elementary, has limit set the whole boundary, contains a
nonabelian free subgroup, and lies inside `R_f(H)`.  So the finite residual of
`H` is itself a non-elementary normal subgroup.

**Why this shape matters.**  It is equivalent to Gromov's question (routes
`residual-prime-torsion-via-free-factor` and
`non-rf-hyperbolic-from-residual-prime-torsion`).  Consequently:

- the central finite-radical alternative of the dichotomy is never needed; any
  attack may assume a trivial finite radical and a non-elementary finite
  residual containing prime torsion;
- ruling out finite nontrivial finite residuals, i.e. ruling out persistent
  degree-two classes (`finite-hyperbolic-residual-iff-persistent-class`), does
  **not** settle the problem, because a counterexample with finite residual
  converts into one of this shape, whose residual is infinite.

## Attempts

- **From any non-residually-finite hyperbolic group.**
  `residual-prime-torsion-via-free-factor` is a complete derivation (filling,
  then a free factor `Z`).  So this claim is exactly as hard as the root.
- **Directly.**  One would need a prime-order element whose non-elementary
  normal closure is killed by every finite quotient.  No mechanism is known;
  the non-sofic compression mechanism is excluded in hyperbolic ambient groups
  by the centralizer rigidity recorded in
  `research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md`, §B.1.
