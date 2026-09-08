---
rg: 2
id: rank-weighted-cutoffs-prove-finite-support-collapse
kind: route
title: Average nested finite supports and apply Kazhdan transport in the rank-weighted Hilbert spaces
target: uniform-finite-support-rank-gap-upgrades-compression-collapse
requires:
  - scaled-kazhdan-transport
  - finite-group-opnorm-support-profile
artifacts:
  - research/artifacts/rank-weighted-locally-finite-compression-2026-09-08.md
---

Sections 2--4 of the artifact give the complete proof. Exactify one
containing finite subgroup per coordinate. Its nested active
projections have rank at most C times the surviving mark rank r_n.
Averages e_n over successively conjugacy-enlarged stages satisfy
e_n p_a=p_a, rank(e_n)<=C r_n, and ||[e_n,V_n(g)]||_op->0.
The actual commutator rank is at most 2C r_n, so it tends to zero
also in the norm |x|_n=(Tr(x*x)/r_n)^(1/2).

The established scaled transport theorem applies with weight w_n=r_n:
its mass-bound hypothesis is Tr(x_n*x_n)=O(r_n), and its vanishing
hypothesis is exactly |[V_n(h),x_n]|_n->0. Apply it to V_n(c)e_n,
which is bounded in |.|_n. This makes every
compression-defect generator vanish after multiplication by e_n.
Quasicentrality shows these vanishing elements form a normal subgroup.
The mark cannot vanish: e_n is the identity on its nontrivial
spectral subspace, giving |(V_n(a)-I)e_n|_n>=eta_m>0.
