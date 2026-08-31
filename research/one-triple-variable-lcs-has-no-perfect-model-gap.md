---
rg: 2
id: one-triple-variable-lcs-has-no-perfect-model-gap
kind: claim
title: One occurrence-three variable cannot create a perfect finite-versus-commuting LCS gap
artifacts:
  - research/one-triple-variable-component-decomposition-proof.md
distinct_from:
  degree-two-operator-ports-are-boundary-edges: that closes the occurrence-at-most-two class; this is the first hypergraph column beyond graph incidence.
  two-port-magic-square-commutator-is-holonomy-square: that treats two ports in one K_(3,3) cell; this handles an arbitrary LCS incidence skeleton with one triple-used variable.
  cyclic-occurrence-splitting-makes-every-lcs-cubic: that shows many occurrence-three variables recover full LCS expressiveness; this proves one such variable is insufficient.
---

Let `L` be a finite binary LCS in which one involution `z` occurs in exactly
three distinct equations and every other variable occurs in at most two.
Let `Gamma_L` be its solution group with central sign `J`.  Then

```text
J != 1 in Gamma_L
  iff
some finite-dimensional representation has J -> -I.
```

Equivalently, `L` has a perfect commuting-operator strategy if and only if
it has a perfect finite-dimensional strategy.  Thus the first
non-incidence column does **not** yet create the desired perfect-model gap.

Delete the three occurrences of `z`.  The remaining degree-two variables
form graph-incidence components.  Distribute the three marked contexts
among those components.  Up to order the only nonzero patterns are

```text
3,      2+1,      1+1+1.
```

A connected component with one `z`-port has an exact dichotomy:

- if its incidence graph is planar, a planar boundary picture pins
  `z=J^p`, where `p` is the parity of its scalar vertex signs;
- if it is nonplanar, it extends every source involution `z` after a finite
  amplification, by spectral control of the two scalar port signs and
  Arkhipov's theorem.

A component with two occurrences of `z` is already a closed graph-incidence
system: `z` is the edge joining the two marked contexts.  A component with
three occurrences always has a scalar solution, because its ordinary
incidence columns span the even-parity vectors and the weight-three `z`
column toggles parity.

These facts settle all three distributions.  In the `2+1` case, use
Arkhipov's finite-dimensional witness for the two-occurrence component; the
one-port component either absorbs its `z` or pins `z`, in which case apply
Arkhipov after taking the corresponding scalar quotient.  In the
`1+1+1` case, planar components pin compatible scalar signs whenever
`J!=1`, while every nonplanar component accepts either scalar sign; tensor
the resulting finite models.  Components not meeting `z` are ordinary
graph-incidence systems and are handled independently.

The exact residual is at least **two** occurrence-three variables (or one
variable of higher occurrence/non-parity syntax).  A single triple diagonal
amalgam is still perfect-model tame.
