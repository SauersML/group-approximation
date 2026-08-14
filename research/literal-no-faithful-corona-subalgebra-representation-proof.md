---
rg: 2
id: literal-no-faithful-corona-subalgebra-representation-proof
kind: route
title: Complement-correct a nonunital corona inclusion
target: literal-no-faithful-corona-subalgebra-representation
requires: [literal-central-mark-corona-invisible]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralNonMFConsequences.lean
  - GroupApproximation/Analysis/MFAlgebra.lean
---

## Why sufficient

For an injective, possibly nonunital, star homomorphism `e : A -> Q`, the
formula

\[
u\longmapsto e(u)+(1-e(1))
\]

is an injective homomorphism `U(A) -> U(Q)`: the two summands occupy the
orthogonal corners cut out by `e(1)` and `1-e(1)`.  Composing it with a
putatively injective representation `E -> U(A)` would give an injective
corona representation of `E`.  This contradicts
`literal-central-mark-corona-invisible`, because the resulting map kills the
nontrivial marked involution.  The exact natural-dimension statement is
`literal_no_faithful_corona_subalgebra_target`; restricting the canonical
faithful group-unitary maps gives the two group-C-star embedding
consequences.
