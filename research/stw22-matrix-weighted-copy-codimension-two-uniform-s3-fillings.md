---
rg: 2
id: stw22-matrix-weighted-copy-codimension-two-uniform-s3-fillings
kind: claim
title: Two unused matrix dimensions give uniform three-sphere fillings, while one is sharply obstructed
distinct_from:
  stw22-matrix-weighted-copy-uniform-s2-fillings: that theorem fills two-spheres with only one unused dimension; the present theorem identifies the new codimension-two threshold in degree three and proves a uniform filling theorem above it.
  stw22-all-finite-factor-weighted-copy-uniform-s2-fillings: that theorem is uniform over all finite factors but stops in degree two; the present theorem is matrix-specific and reaches degree three.
  stw22-multicopy-fibres-collapse-and-zero-slack-obstructs-lc1: that theorem finds the determinant-loop obstruction at zero slack; the present theorem finds an SU(2) three-sphere obstruction at positive rank-one slack.
artifacts:
  - research/artifacts/stw22-matrix-lc3-codimension-barrier-audit-2026-08-31.md
---

Equip M_n with normalized trace and finite tuples with the Hilbert-sum
2-metric.  Let a be a positive contraction, put p=supp(a), and assume the
m-copy fibre is nonempty.  Its total polar source rank and unused target
rank are

    k=m rank(p),       c=n-k.

If a=0, the fibre is a singleton.  If c>=2, put
epsilon_0=min(epsilon,1).  Every continuous map

    S^3 -> F_(n,m)(a)

whose image lies in the ball of radius

    rho_3(epsilon)=epsilon_0^3/276480

about one point of the fibre extends over B^4 inside the concentric
epsilon-ball.  The modulus is independent of n, m, a, k, and c.  Every
such fibre is globally 3-connected.  Together with the degree-zero,
degree-one, and degree-two estimates, the family with c>=2 is uniformly
equi-LC^3.

The projection core has the quadratic modulus

    rho_(3,St)(epsilon)=epsilon_0^2/2560

for St_n(q) whenever rank(1-q)>=2.

The codimension hypothesis is sharp.  If k>0 and c=1, then

    pi_1(V_k(C^n))=pi_2(V_k(C^n))=0,
    pi_3(V_k(C^n))=Z.

More strongly, for n>=3 and q_n=diag(I_(n-1),0), the map

    Phi_n:SU(2)=S^3 -> St_n(q_n),
    Phi_n(g)=diag(g,I_(n-2))q_n

is a generator of pi_3 and satisfies

    sup_g ||Phi_n(g)-q_n||_(2,n) <= sqrt(8/n).

Thus essential three-spheres occur in arbitrarily small normalized
2-balls while the support slack is still positive:
tau(q_n)=1-1/n.  Consequently no three-sphere filling modulus can be
simultaneously uniform in matrix size and in arbitrarily small positive
slack for the full merely-strictly-slack family.

This obstruction does not occur in the half-slack replication regime used
to kill fibre-gap traces.  If m>=2, a!=0, and

    m tau(p)<=1/2,

then k>=2, n>=4, and c=n-k>=n/2>=2.  Hence every nonzero matrix fibre in
that regime lies in the positive half of the theorem.
