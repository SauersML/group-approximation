---
rg: 2
id: modular-machine-halting-invariance-proof
kind: route
title: Determinism of the quadruple table, transported to integer indices
target: modular-machine-halting-invariance
requires: []
artifacts:
  - GroupApproximation/Computability/BooneGroupModularMachine.lean
---

## Direct proof, machine-checked

A modular machine of size `M > 1` carries its quadruple table as a *function*
`quad : N -> N -> Option (N x Bool)` of the two residues, so determinism is
structural rather than an axiom: `step` reads `(lo a, lo b)`, and the two
`Bool` cases write `hi a * M^2 + c` into one coordinate and keep `hi` of the
other.  The side conditions are `quad_eq_none_left`/`_right` (only residues
below `M` carry quadruples), `quad_lt` (`c < M^2`) and `quad_zero_zero`.

**`halts_iff_of_step`.**  `Halts p` is `Reaches p (0,0)`, the reflexive
transitive closure of `step`.  Since `step` is a partial *function*, the
successor of a configuration is unique, so reachability of `(0,0)` from `p`
and from its successor agree -- backwards by prefixing the step, forwards by
`Relation.ReflTransGen.cases_head` on a run out of `p`, where the first step
is forced.  The forward direction is where `quad_zero_zero` is needed: without
it `p = (0,0)` halts trivially while its successor need not.

**The two `haltsZ` forms.**  The group construction indexes the free basis of
`T` by `Z x Z`, not `N x N`, and applies the machine along the parametrised
families `(a + uM, b + vM)`.  `haltsZ_right_iff` and `haltsZ_left_iff` are
`halts_iff_of_step` composed with those parametrisations, with the arithmetic
of residues discharged explicitly; the bound `c < M^2` is what keeps the image
in the right residue class when the parameter is negative.

Nothing here is conditional, and no machine is exhibited: the statements are
universally quantified over modular machines.  Exhibiting one whose halting
set is non-computable is a different obligation, deliberately not stated in
Lean anywhere in this chain -- see
[[modular-machine-with-noncomputable-halting]].
