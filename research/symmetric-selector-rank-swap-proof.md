---
rg: 2
id: symmetric-selector-rank-swap-proof
kind: route
title: Decompose the signed four-point gauge action in both reset signs
target: symmetric-selector-rank-swap-has-balanced-restriction
requires:
  - symmetric-selector-schur-residual-packet
  - four-point-gauge-orbit-has-balanced-derived-rank-swap
---

In `Sigma`, the element `J_x` is `-1` on the coordinate line `x` and `+1`
on every other coordinate line.  Products of the `J_x` therefore give the
full diagonal sign group on `l2(X)`, while `Sym(X)` gives the full permutation
group.  Thus every signed permutation used in the four-point construction is
an ordinary element of the finite group `G`.

On one coset of `span(u,v)`, diagonalize the half-turn `tau_v`.  Its two
eigenspaces both have dimension two.  Equations `(GRS1)--(GRS2)` show that on
the negative eigenspace `(p_-,q_-)` is one Pauli pair and `(p_+,q_+)` is
trivial, while on the positive eigenspace the roles reverse.  This gives the
two irreducible two-dimensional types `R_-` and `R_+` in `(SBR4)`.

There are four cosets, so each type occurs four times.  The signed-permutation
packet acts only on `l2(X)` and the standardized residual acts only on
`H_res`; tensoring the two decompositions proves `(SBR5)`.  Restriction of a
two-dimensional rank-swap type to the residual forgets its two-dimensional
factor, hence gives two copies of `rho` in both signs.  This is the required
equal branching multiplicity.
