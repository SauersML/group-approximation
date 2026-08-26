---
rg: 2
id: mapping-torus-mf-radical-lies-in-finite-residual
kind: claim
title: The finite residual bounds every automorphism mapping-torus MF radical
distinct_from:
  finitely-generated-rf-automorphism-mapping-torus-is-rf: That assumes the whole kernel is residually finite and concludes that the whole mapping torus is residually finite; this allows an arbitrary finitely generated kernel and bounds the mapping-torus MF radical by its finite residual.
  split-cyclic-kazhdan-defect-exact-mf-radical: That is the positive assembly criterion for an exact kernel radical; this proves the universal necessary condition that such a kernel have no nontrivial finite quotient.
  finite-outer-order-mapping-torus-is-virtually-product: That obstructs actions of finite outer order; this applies to every automorphism without restricting its outer order.
artifacts:
  - research/torsion-free-lef-kazhdan-non-rf-seed.md
  - research/artifacts/torsion-free-exact-radical-team-audit-2026-08-26.md
---

Let `K` be finitely generated, let `phi` be an automorphism of `K`, and put

```text
G = K semidirectProduct_phi Z.
```

If `R_fin` denotes the finite residual, then it is computed exactly by

```text
R_fin(G) = R_fin(K) x {0},
Rad_MF(G) <= R_fin(K) x {0}.                            (FRB1)
```

Consequently, if `Rad_MF(G)=K x {0}`, then

```text
R_fin(K)=K;                                             (FRB2)
```

equivalently, `K` has no nontrivial finite quotient.  This is a necessary
condition for every exact-kernel construction in
`torsion-free-sofic-exact-mf-radical-over-z`, independent of the chosen
compression mechanism, finite presentation, torsion-freeness or soficity.

More generally, if `A` is any `phi`-invariant normal subgroup for which
`K/A` is residually finite, then

```text
Rad_MF(G) <= A x {0}.                                   (FRB3)
```

This applies to the characteristic-zero Kida--Thom seed
`torsion-free-lef-kazhdan-non-rf-seed`.  In its central extension

```text
1 -> A=C/C_+ -> K -> Gamma_0 -> 1,
```

the subgroup `A` is exactly `Z(K)`, hence characteristic, while `Gamma_0` is
finitely generated and residually finite.  Therefore every
`phi in Aut(K)` satisfies

```text
Rad_MF(K semidirectProduct_phi Z) <= Z(K) < K.           (FRB4)
```

Thus neither the Laurent shift nor any companion-matrix refinement, nor any
other automorphism of this seed, can solve the target.  The same universal
test eliminates every candidate seed having any nontrivial finite quotient.
