---
rg: 2
id: fanizza-regular-trace-heat-domination-compiler
kind: claim
title: Compile the fixed Fanizza mark below every heat amplitude in canonical trace
refuted_by: computable-regular-trace-fanizza-return-would-decide-halting
distinct_from:
  fanizza-depthwise-fixed-mark-return: that requests explicit finite-matrix inequalities with relator and trace-window errors; this asks only for the corresponding regular canonical-trace inequalities, from which those estimates follow automatically.
  fanizza-native-signal-groupification: that requires an unconditional quantitative decoder on matrix tuples; this is conditioned on the canonical group trace and permits arbitrary depth loss.
  fanizza-heat-filter-one-sided-return: that seeks a finite-coordinate cyclic or Julia return; this removes the block decoder entirely and isolates an algebraic/canonical-trace compiler.
---

**REFUTED.**  The proposed target was: totally computably from `m`, construct a uniformly recursively
presented ordinary group `Gamma_m`, a fixed rational group-algebra mark
`P_m`, and the native Fanizza heat expressions `A_(m,t)` such that

```text
m HALT     => P_m!=0 in one exact representation,                  (RHC1)
m NONHALT  => tau_(Gamma_m)(P_m^*P_m)
              <=tau_(Gamma_m)(A_(m,t))       for every t>=1.       (RHC2)
```

Then `canonical-moments-linearize-fixed-depth-fanizza-return` supplies
`(DFR1)` for each fixed `t`, with arbitrary finite depth-dependent constants.
Together with the fixed-depth heat bound, `(RHC2)` collapses the mark and
closes the canonical-profile reverse-Kleene route.

## Attempts

- **Why this is strictly smaller.**  No multiplicity selector, Julia
  dilation, cyclic product, additive coefficient decoder, or endogenous
  dimension tape occurs in `(RHC1)--(RHC2)`.  Only the coefficient of the
  identity in two finite rational group-algebra expressions matters at each
  depth.
- **The direct quotient idea exposes the exact algebraic gate.**  In the
  native NONHALT theorem, `D_R<=C_m H_m`.  If an ordinary-group compiler
  made the positive verifier Hamiltonian vanish in the relevant quotient
  while retaining the HALT perfect representation, then `P_m=D_R` would
  vanish on NONHALT instances and `(RHC2)` would be immediate.  The missing
  operation is precisely ordinary-group encoding of the native nonaffine BCS
  constraints; parity/solution-group relators encode only affine support.
- **Canonical support does not wordize the Julia unitary.**  Formula `(CMF7)`
  gives a fixed regular `L^2` floor between a group word and every genuinely
  multiword Julia or heat expression.  A wandering word helps only if new
  relations first prove `(RHC2)`; normal-form orthogonality alone points in
  the opposite direction.
- **Fatal computability obstruction.**  Applying all depths of `(RHC2)` and
  the heat estimate forces `P_m=0` in the NONHALT group algebra, while
  `(RHC1)` forces `P_m!=0` on HALT instances.  Group-algebra zero over a
  uniformly recursively presented group is recursively enumerable.  Hence
  this would enumerate both HALT and NONHALT and decide the halting problem;
  `computable-regular-trace-fanizza-return-would-decide-halting` gives the
  full proof.  The regular firewall cannot be promoted to the target.
