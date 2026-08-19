---
rg: 2
id: iwahori-nielsen-extension-transversality
kind: claim
title: Isolated near-unitary Iwahori types have dimension-free transversality between opposite extension loci
distinct_from:
  iwahori-commensurator-nielsen-involution: That established theorem merely identifies the two opposite extension loci under an explicit involution; this claim asks for a quantitative metric-regularity theorem near one isolated high-dimensional type pair.
  iwahori-fractional-transport-integralization: That is the global operator-valued matching problem which extracts orthogonal near-unitary block pairs from a fractional transport; this claim starts after one such pair of irreducible edge types has already been isolated.
  iwahori-outlier-repair: That is the complete central-regular endpoint, including physical mass localization, integralization and assembly across all blocks; this claim is only the local correction of one matched irreducible type pair.
artifacts:
  - docs/FALSE_ROBUST_T_IWAHORI_EDGE_REPAIR.md
  - docs/TRUE_IWAHORI_FACTOR_GATE_IS_COSYSTOLIC_ANGLE.md
  - docs/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md
---

Let `Kbar=PSL_2(Z)` and `Bbar=<u,e | e^2=1> ~= Z*C_2` be the upper Iwahori
subgroup.  Let `alpha` be the explicit involution from
`iwahori-commensurator-nielsen-involution`.

Consider irreducible `Bbar`-representations `theta_n,eta_n` of the same
physical dimension `r_n->infinity`, together with irreducible modular vertex
representations `pi_n^+,pi_n^-` such that

```text
theta_n occurs in pi_n^+|Bbar,
alpha^*(eta_n) occurs in pi_n^-|Bbar.
```

(The index-three theorem makes these occurrences multiplicity one and bounds
the parent dimensions between `r_n` and `3r_n`.)  Suppose there are unitaries
`U_n` between the two edge spaces with

```text
max_(s in S_B) ||theta_n(s)U_n-U_n eta_n(s)||_(2,r_n) -> 0
```

for one fixed finite generating set `S_B`.

Ask for a dimension-independent flexible **local transversality** modulus:
after adding/deleting `o(r_n)` dimensions to the two parent vertex blocks,
perturb `pi_n^+,pi_n^-` by `o(1)` in normalized Hilbert--Schmidt distance to
exact modular vertex representations whose selected Iwahori constituents are
unitarily identical under the prescribed commensuration.  Equivalently, the
near pair `(theta_n,eta_n)` should be `o(1)`-close, after negligible flexible
stabilization, to one irreducible type lying in the actual intersection of
the upper extension locus with the `alpha`-twisted extension locus.

This is deliberately **local**: one matched irreducible edge pair is supplied
as input.  It says nothing about turning the global fractional overlap of two
large reducible edge representations into such orthogonal pairs; that is
`iwahori-fractional-transport-integralization`.

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
