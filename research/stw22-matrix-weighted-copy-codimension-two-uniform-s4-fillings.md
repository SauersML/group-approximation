---
rg: 2
id: stw22-matrix-weighted-copy-codimension-two-uniform-s4-fillings
kind: claim
title: Codimension-two matrix weighted-copy fibres have dimension-free uniform four-sphere fillings
distinct_from:
  stw22-matrix-weighted-copy-codimension-two-uniform-s3-fillings: that theorem reaches degree three by cancelling c_1 on a carrier skeleton; the present theorem reaches degree four and cancels the new localized c_2 obstruction with a rank-two Bott absorber.
  stw22-matrix-weighted-copy-uniform-s2-fillings: that theorem needs only one unused target dimension and stops in degree two; the present theorem needs two unused dimensions and reaches degree four.
  stw22-diffuse-stiefel-uniform-three-sphere-fillings: that theorem is diffuse and degree three; the present theorem is finite-dimensional and degree four.
artifacts:
  - research/artifacts/stw22-matrix-lc4-bott-cancellation-audit-2026-08-31.md
---

Equip M_n with normalized trace and finite tuples with the Hilbert-sum
2-metric.  Let a be a positive contraction, put p=supp(a), and write

    k=m rank(p),       c=n-k.

If a=0 the weighted-copy fibre is a singleton.  If c>=2, then, with
epsilon_0=min(epsilon,1), every continuous map

    S^4 -> F_(n,m)(a)

whose image lies in the ball of radius

    rho_4(epsilon)=epsilon_0^3/276480

about one point of the fibre extends over B^5 inside the concentric
epsilon-ball.  The modulus is independent of n, m, a, k, and c.

Every such fibre is globally 4-connected.  Together with the established
degree-zero through degree-three estimates, the codimension-two family is
uniformly equi-LC^4.

For projection weights, if q in M_n and rank(1-q)>=2, the quadratic
modulus

    rho_(4,St)(epsilon)=epsilon_0^2/2560

works for St_n(q).

The integer codimension is topologically sharp for the full equi-LC^4
package.  When the source is nonzero and c=1, the fibre already has
pi_3=Z, so it is not 4-connected.  No claim is made that every individual
S^4 map in codimension one is obstructed.

In particular, if m>=2, a!=0, and m tau(p)<=1/2, then c>=2.  Thus every
nonzero matrix fibre in the half-slack replication regime used by
fibre-gap trace arguments satisfies the theorem.  The matrix branch is
therefore ready through selection degree four; an all-factor
dimension-five trace theorem would additionally require the corresponding
diffuse degree-four input.
