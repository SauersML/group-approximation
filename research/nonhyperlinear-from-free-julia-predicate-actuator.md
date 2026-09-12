---
rg: 2
id: nonhyperlinear-from-free-julia-predicate-actuator
kind: route
title: Apply the finite game gap to the canonically massive free Julia Gram block
target: non-hyperlinear-group
requires:
  - oracularizable-tracial-nonru-game-exists
  - one-gram-vector-decodes-a-finite-bcs-strategy
  - free-julia-grading-carries-one-gram-at-canonical-quarter-mass
  - free-julia-nonlinear-predicate-actuator
---

Let `w_0=zjzj`.  Exact completeness of the actuator gives a representation
with `w_0!=1`, so the corresponding element is nontrivial in the compiled
group.

Assume the group hyperlinear and take canonical microstates.  After fixed
involution and commutation rounding, `(FJG5)` gives

```text
||G||_2^2=1/4+o(1).                                    (NFJ1)
```

Every consistency relator `d_xjd_xj=1` and `(FJG4)` give

```text
sum_(c,x) mu_(c,x)||A_xG-GB_x||_2^2=o(1).             (NFJ2)
```

The actuator inequality `(FJPA2)` gives

```text
sum_c mu_c||F_cG||_2^2=o(1).                           (NFJ3)
```

Thus the total one-Gram game energy is `o(1)`.  But
`one-gram-vector-decodes-a-finite-bcs-strategy` and the finite game gap give

```text
E_G >= (1-theta)||G||_2^2=(1-theta)/4+o(1),           (NFJ4)
```

a contradiction.  Hence the compiled group is non-hyperlinear.

