---
rg: 2
id: dimension-reported-schur-replica-halting-compiler
kind: claim
title: A halting output dimension activates a uniformly sound supercritical Schur-replica table
distinct_from:
  adaptive-all-pairs-schur-replica-table-compiler: that requires one fixed group to inspect each candidate residual matrix factor and choose its replica count internally; this lets the source machine print the dimension before the finite challenge is activated.
  constant-hs-groupification-of-residual-dimension-tape: that uses polynomial identities to discover residual dimension from operator data; this receives the target dimension as ordinary finite computation output and uses no matrix identity.
---

Construct a total computable machine-to-group compiler with universal
constants `delta>0` and `alpha<sqrt(2)` satisfying `(DMK1)` and the following
halting clause.

If the source machine halts and outputs `D`, its finite control computes

```text
N>b_epsilon^(-1) log_2(D/(1-4epsilon^2))                         (DRC1)
```

for one fixed sufficiently small `epsilon`.  Every `D`-dimensional tuple for
the compiled presentation with relator defect below `delta` and marked
distance above `alpha` must then decode to:

1. `N` commuting replicas of the fixed non-CE BCS tuple;
2. one selected context of forbidden mass at least `beta_B/C` per replica;
3. an all-pairs `epsilon`-homomorphism of the finite central product of the
   selected Schur context packet/flip groups; and
4. the forbidden Fourier masses `(ASE1)` on one common marked carrier.

By `(ASE2)` and `(DRC1)`, such a `D`-dimensional tuple cannot exist, giving
`(DMK2)` exactly in the reported dimension.

All semantic losses must be bounded by the universal `delta,alpha,epsilon`,
independently of `D`, `N`, and the halting runtime.  If the machine never
halts, an exact tracial model must retain `w_M!=1`; dormant challenge hardware
may not collapse the mark.

## Attempts

- Ordinary Boone/S-machine simulation accumulates error with halting time and
  does not give universal `delta`.
- Writing the finite `N`-replica table after halting is syntactically
  computable, but a fixed finite presentation must verify that generated table
  with constant soundness rather than one relator per simulated step.
- Dinur amplification and recursive game compression provide the intended
  runtime-independent verifier architecture.  The unresolved lowering is
  perfect-complete translation of the verifier's local checks to the selected
  Schur packet multiplication table and then to group words.
- Unlike the residual dimension-tape routes, no operator-level dimension
  sensor is missing here: the recursion-theorem search itself supplies `D`.

