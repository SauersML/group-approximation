---
rg: 2
id: stw59-prescribed-commutator-component-groups
kind: claim
title: Simple AH algebras realize independent central commutators of orders n·C(n-1,i-1) in their unitary component groups
distinct_from:
  stw59-nonabelian-unitary-component-groups: That is one commutator pair of order n with central kernel Z/n!; this puts several independent pairs, of every order n·C(n-1,i-1), into one simple algebra with kernel a direct sum of factorial groups.
  gauge-components-over-circle-sphere-towers: That is the finite-stage group over one arm S^1 x S^(2n-1); this is the simple limit over wedges of arms S^(2i-1) x S^(2j-1).
artifacts:
  - research/artifacts/stw59-samelson-orders-and-wedged-arms-2026-09-11.md
---

Take any finite list (n_α, i_α) with n_α>=2 and 1<=i_α<=n_α, and set
N_α = n_α·C(n_α-1, i_α-1). There are a separable simple unital nuclear
stably finite AH algebra B, with unique trace and stable rank two, and
unitaries u_α, v_α in B such that:

- U(B)/U0(B) -> K1(B) is surjective with central kernel
  direct-sum_α Z/n_α!;
- [u_α, v_α] has order exactly N_α and lies in coordinate α of the kernel,
  while distinct pairs commute pointwise;
- K1(B) is free abelian of countably infinite rank.

With i_α=1 and n_α=d_α, the commutator subgroup contains the prescribed
finite abelian group direct-sum Z/d_α. For n=3 and i=2 the S^3 x S^3
commutator generates the whole kernel Z/6.

Complete proof from the lix-sweep lane; not independently reviewed.

ROUTES

stw59-prescribed-commutators-wedge-proof
