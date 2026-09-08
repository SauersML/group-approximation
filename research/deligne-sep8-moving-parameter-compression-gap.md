---
rg: 2
id: deligne-sep8-moving-parameter-compression-gap
kind: claim
title: Moving Maslov parameters still have a uniform finite-rank compression gap
artifacts:
  - research/artifacts/deligne-sep8-moving-parameter-compression-gap.md
distinct_from:
  deligne-fixed-projective-representation-folner-compression-no-go: that fixes one odd-sector exact representation; this allows the parameter and representation to vary arbitrarily, including nonzero parameters tending to zero, with one quantitative constant.
  odd-maslov-homogeneous-coefficients-have-a-uniform-folner-gap: that fixes an odd difference multiplier; this treats every parameter outside the exact metaplectic subgroup and gives an explicit bound in terms of a Kazhdan constant of the base.
  deligne-sep8-first-order-tensor-threshold: that identifies the little-o parameter error needed for an all-MF construction; this excludes near-unitary finite-rank compressions of exact projective representations as a way to supply it.
---

Let `b` be the actual integral Deligne covering cocycle. Choose a finite
Kazhdan set `S` for `Gamma=Sp_4(Z)` and a constant `0<kappa<=1` such that
every ordinary unitary representation `rho` without invariant vectors
satisfies

```text
max_(s in S) ||rho(s)xi-xi|| >= kappa ||xi||.
```

For every parameter `t in (R/Z)\{0,1/2}`, every exact
`exp(2 pi i t b)`-projective unitary representation `pi` on a Hilbert space,
and every nonzero finite-rank projection `P`,

```text
max_(s in S) ||[P,pi(s)]||_HS / sqrt(rank P) >= kappa.
```

Writing `A_s=P pi(s) P` on `P H`, one also has

```text
max_(s in S) tr_(P H)(I-A_s^* A_s) >= kappa^2/2,
max_(s in S) inf_(V in U(P H)) ||A_s-V||_op >= kappa^2/4.
```

The constants are independent of the parameter, the exact representation,
and the compression rank. In particular, allowing `t_n->0` through
nonzero parameters and changing the ambient representation at every step
does not permit finite-rank compressions that become unitary after an
operator-norm perturbation tending to zero.

This does not bound the relation defects of arbitrary unitary matrix
tuples. A large change of the compressed generators, including a Toeplitz
symbol correction that stays away from the identity, is outside this
claim and would need an independent scalar-multiplier error analysis.
