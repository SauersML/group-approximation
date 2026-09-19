---
rg: 2
id: stw22-matrix-weighted-copy-uniform-finite-degree-fillings
kind: claim
title: Matrix weighted-copy fibres have sharp dimension-free fillings in every finite degree allowed by codimension
distinct_from:
  stw22-matrix-weighted-copy-codimension-two-uniform-s4-fillings: that theorem treats only degree four and codimension two; the present theorem gives every fixed finite degree and the sharp inequality 2c>=j.
  stw22-matrix-weighted-copy-uniform-s2-fillings: that theorem gives a sharper low-degree constant when c>=1; the present theorem supplies the general carrier and Bott-promotion induction.
  stw22-diffuse-weighted-copy-all-finite-sphere-fillings: that theorem is for diffuse finite factors; the present theorem is the normalized matrix branch and records the sharp shrinking Bott spheres below the codimension range.
artifacts:
  - research/artifacts/stw22-matrix-finite-degree-carrier-induction-audit-2026-08-31.md
---

Fix an integer j>=2 and put

    t=floor((j-1)/2),        r=floor(j/2),
    A_j=t(t+1)/2,            C_j=j+1+A_j+r.

Equip M_n with normalized trace and finite tuples with the Hilbert-sum
2-metric.  Let a be a positive contraction, put p=supp(a), and write

    k=m rank(p),             c=n-k.

If a=0 the weighted-copy fibre is a singleton.  If a is nonzero and

    2c>=j,                                                    (FD-1)

then, with epsilon_0=min(epsilon,1), every continuous map

    S^j -> F_(n,m)(a)

whose image lies in the ball of radius

    rho_j(epsilon)=epsilon_0^3/(276480 C_j)                  (FD-2)

about one point extends over B^(j+1) inside the concentric
epsilon-ball.  The modulus depends only on j and epsilon: it is
independent of n, m, a, k, c, and the amount of positive slack.

Every fibre satisfying (FD-1) is globally j-connected.  Applying the
statement degree by degree gives a uniformly equi-LC^j family whenever
the corresponding codimension inequalities hold.  The assertion is
per fixed finite degree; it does not assert one positive modulus
uniform in j.

For projection weights, if q has rank k and rank(1-q)=c with 2c>=j, the
quadratic modulus

    rho_(j,St)(epsilon)=epsilon_0^2/(2560 C_j)               (FD-3)

works for St_n(q).  The previously established degree-two, degree-three,
and degree-four theorems have sharper constants in their stated ranges.

The codimension inequality is topologically sharp.  For every c>=1 and
n>c, the first nonzero homotopy group of V_(n-c)(C^n) is

    pi_(2c+1)(V_(n-c)(C^n))=Z.

It has a generator represented by a sphere contained in the normalized
2-ball of radius 2/sqrt(n) about the standard frame.  Taking n to
infinity with c fixed gives essential spheres of shrinking radius and
positive slack c/n.  Consequently neither global j-connectivity nor a
joint dimension-free equi-LC^j statement can extend past 2c>=j.

There is a useful trace corollary.  If a!=0,

    m tau(p)<=1/2       and       m>=ceil(j/2),

then c>=m and hence 2c>=j.  Thus, after choosing the replication number
for a fixed finite selection degree, no matrix factor obstructs that
degree in the half-slack fibre-gap regime.
