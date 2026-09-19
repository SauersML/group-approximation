---
rg: 2
id: triangular-e5-pulses-admit-persistent-tail-character-proof
kind: route
title: Solve the fresh-leading-coefficient equations recursively
target: triangular-e5-pulses-admit-persistent-tail-character
requires:
  - fanizza-symmetric-kernel-has-two-root-e5-clock
  - free-root-first-detection-eigenvectors-localize-exactly
---

At stage `n`, the equation `ell(p_n)=1` contains the unassigned variable
`ell(x^(2n))` with coefficient one, while every earlier equation has lower
degree.  Assign that variable to satisfy the new equation.  The union of the
finite assignments defines a linear functional on the monomial basis; set
all unused values to zero.

For the finite-depth statement, reduction modulo a polynomial of degree above
all `p_n`, `n<=N`, is injective on their coefficient vectors.  The quotient
ring and its elementary group are finite, and induction from the finite
additive root subgroup is finite-dimensional.  The first-hit theorem is not
contradicted: this character belongs to one early boundary layer; later pulse
negativity does not move it into later first-hit layers.
