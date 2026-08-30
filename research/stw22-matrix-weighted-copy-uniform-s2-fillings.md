---
rg: 2
id: stw22-matrix-weighted-copy-uniform-s2-fillings
kind: claim
title: Matrix weighted-copy fibres have a dimension-free uniform two-sphere filling modulus
distinct_from:
  stw22-matrix-weighted-copy-uniform-loop-fillings: that theorem gives the degree-one filling estimate; the present theorem proves the missing degree-two estimate by a triangulated soft carrier and Chern-class cancellation.
  stw22-fixed-factor-weighted-copy-uniform-s2-fillings: that theorem treats one fixed diffuse factor with a factor-dependent modulus; the present theorem is uniform over every normalized matrix factor.
  stw22-multicopy-fibres-collapse-and-zero-slack-obstructs-lc1: that theorem identifies the Stiefel topology and the zero-slack loop obstruction; the present theorem gives controlled fillings of two-spheres under the sharp qualitative condition of one unused matrix dimension.
artifacts:
  - research/artifacts/stw22-matrix-uniform-s2-filling-audit-2026-08-30.md
---

Equip every matrix algebra M_n with its normalized trace and finite tuples
with the Hilbert-sum 2-metric.  Fix m>=1, gamma>0, and a positive
contraction a in M_n satisfying

    m tau(supp(a)) <= 1-gamma.

For the exact weighted-copy fibre

    F_(n,m)(a)={(v_1,...,v_m):
                v_j^*v_j=a and the v_jv_j^* are pairwise orthogonal},

put epsilon_0=min(epsilon,1).  Every continuous map

    S^2 -> F_(n,m)(a)

whose image lies in the ball of radius

    rho_2(epsilon)=epsilon_0^3/276480

about one point of the fibre extends over B^3 inside the concentric
epsilon-ball.  The modulus is independent of n, m, gamma, and a.

Every such fibre is 2-connected.  Together with the established
dimension-free path and loop estimates, the strictly-slack matrix
weighted-copy fibres form a uniformly equi-LC^2 family.

The projection core is quadratic.  For every proper projection q in M_n,

    St_n(q)={v in M_n:v^*v=q}

has the same two-sphere filling property with

    rho_(2,St)(epsilon)=min(epsilon,1)^2/2560.

Only q!=1 is used.  In particular the estimate remains uniform when
rank(1-q)=1.  The strict slack in the weighted statement is likewise
qualitative: it supplies one unused target dimension, and its numerical
size does not enter the modulus.
