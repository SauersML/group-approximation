---
rg: 2
id: perfect-lamp-compression-and-finite-orbit-sofic-proof
kind: route
title: Use distinct compressed lamp sites and finite level orbits to prove the conditional wreath corollary
target: kazhdan-self-embedding-has-sofic-perfect-lamp-non-mf-family
requires:
  - locally-finite-centralizer-derived-subgroup-is-mf-invisible
artifacts:
  - research/artifacts/compression-locally-finite-centralizer-criterion-2026-09-08.md
---

Sections 5--7 provide all the group and permutation calculations.
The initial lamp centralizes `L`. Choose `ell in L\uLu^-1`;
the two lamps at `uL` and `ell uL` are distinct and commute.
The prerequisite kills the derived subgroup of the initial lamp,
hence its whole perfect group and all its translates. The height
map shows the coset set is infinite. A finite normal lamp subgroup
would have a finite nonempty invariant union of supports, impossible
in this transitive infinite action.

The levels `L_j=u^-j L u^j` exhaust `N`. The finite-index hypothesis
makes every `L_j` orbit on `H/L` finite. Restricting lamps to such
finite orbits, together with finite quotients of `L_j`, proves that
`B^(H/L) semidirect L_j` is residually finite. Their union `R` is
locally residually finite and `W=R semidirect Z`. The artifact gives
permutations on an integer interval times a finite quotient of a
subgroup containing all tested translates. Multiplication fails only
at wrap points of density tending to zero; separation holds on every
fiber for nontrivial zero-height elements and follows from the shift
for nonzero height. This proves soficity directly.

Under the additional hypothesis that `H` is residually finite, its
finite permutation quotients embed it in a norm matrix corona. Thus
the quotient by the base gives the upper MF-radical bound. Finite
quotients also kill the compression defect in `H`, giving the upper
defect bound in `W`. The defects `b_(uL)b_(ell uL)^-1`, commuted
with lamps at `uL`, give all lamp commutators. Perfectness and
transitivity give the reverse bound. These arguments do not assume
residual finiteness of an arbitrary ascending HNN extension.
