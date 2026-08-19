---
rg: 2
id: iwahori-nielsen-extension-transversality
kind: claim
title: Near-unitary Iwahori pairs have dimension-free transversality between E and alpha-star E
distinct_from:
  iwahori-commensurator-nielsen-involution: That established theorem merely identifies the two opposite extension loci as E and alpha-star E under an explicit involution; this claim asks for a quantitative metric-regularity theorem for their near intersections.
  iwahori-fractional-transport-integralization: That is the global operator-valued matching problem which extracts orthogonal near-unitary block pairs; this claim starts after one such matched pair has already been isolated.
  iwahori-outlier-repair: That is the global central-regular endpoint, including fractional mass localization and assembly across all blocks; this claim is only the local extension-locus correction for an already isolated near-unitary pair.
artifacts:
  - docs/FALSE_ROBUST_T_IWAHORI_EDGE_REPAIR.md
  - docs/TRUE_IWAHORI_FACTOR_GATE_IS_COSYSTOLIC_ANGLE.md
---

Let `Kbar=PSL_2(Z)` and `Bbar=<u,e | e^2=1> ~= Z*C_2` be the upper Iwahori
subgroup.  Let `E_d` be the set of `d`-dimensional unitary representations of
`Bbar` which extend to `Kbar`, modulo unitary conjugacy, and let `alpha` be the
explicit involution from `iwahori-commensurator-nielsen-involution`.

Ask for a dimension-independent flexible transversality modulus with the
following local form.  Suppose

```text
theta_n in E_(d_n),
eta_n in alpha^* E_(d_n),
U_n in U(d_n),
```

and for a fixed finite generating set `S_B` of `Bbar`,

```text
max_(s in S_B) ||theta_n(s) U_n-U_n eta_n(s)||_2 -> 0.
```

Then, after stabilization by `o(d_n)` dimensions, there should exist a
representation

```text
zeta_n in E_(D_n) intersect alpha^* E_(D_n),
D_n=d_n+o(d_n),
```

and stabilized vertex extensions of `theta_n` and `eta_n` whose restrictions
move by `o(1)` in normalized Hilbert--Schmidt distance to `zeta_n`.

Equivalently: a near-unitary almost intersection of the two symmetric
extension loci `E` and `alpha^*E` must lie, flexibly and with a
dimension-free modulus, near their actual intersection.

This is deliberately **local**.  It assumes the global Iwahori mismatch has
already been integralized into orthogonal near-unitary pairs; it does not ask
how to obtain those pairs from the fractional block transport.

## Attempts

1. **Use robust property `(T)` of the ambient amalgam.**  Closed by
   `docs/FALSE_ROBUST_T_IWAHORI_EDGE_REPAIR.md`: the edge group is virtually
   free and the mixed representation has no uniform internal gap, while the
   ambient adjoint scalar line is fixed for the wrong reason.
2. **Use ordinary local rigidity of the representation variety.**  A local
   implicit-function theorem has constants depending on the positive
   singular values of the Bass--Serre restriction map.  The missing statement
   is precisely a dimension-uniform lower bound modulo its kernel, together
   with basin capture; `docs/TRUE_IWAHORI_FACTOR_GATE_IS_COSYSTOLIC_ANGLE.md`
   isolates this as the cosystolic-angle problem.
3. **Exploit only `alpha^2=id`.**  The involution makes the two loci symmetric
   and is useful structure, but symmetry alone does not prevent two
   high-dimensional algebraic strata from approaching each other while their
   actual intersection remains far away.  A quantitative transversality input
   is still required.
