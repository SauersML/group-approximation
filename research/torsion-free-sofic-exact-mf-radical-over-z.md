---
rg: 2
id: torsion-free-sofic-exact-mf-radical-over-z
kind: claim
title: A torsion-free finitely presented sofic group has a proper Kazhdan MF radical with quotient Z
root: true
goal: true
distinct_from:
  torsion-free-finitely-presented-non-mf: That established existence theorem supplies torsion-freeness and finite presentation but its known witness is nonsofic and has full, rather than proper, MF radical.
  literal-mf-radical-is-unsquared-defect: The literal group is finitely presented and sofic with an exact proper radical, but it has Clifford two-torsion and its radical is not a Kazhdan torsion-free kernel.
  compression-wreath-five-radicals-coincide: Those sofic finite-perfect-lamp examples have exact proper radicals but contain finite torsion, are only finitely generated, and their radicals are locally finite rather than Kazhdan.
  defect-saturation-full-mf-radical: That gives a finitely presented torsion-free Kazhdan group with full MF radical; soficity is not known and there is no visible quotient.
  simple-sofic-total-mf-radical: That gives a countable simple sofic full-radical group but supplies neither finite presentation, torsion-freeness, nor property (T).
artifacts:
  - research/split-cyclic-kazhdan-defect-exact-mf-radical.md
  - research/torsion-free-sofic-extrinsic-kazhdan-defect-kernel.md
  - research/fp-kernel-crosses-alekseev-thom-open-problem.md
  - GroupApproximation/Kazhdan/KazhdanFiniteGeneration.lean
  - research/artifacts/torsion-free-full-mf-radical-2026-08-19.md
---

There exist a group `G` and a subgroup `K normal G` such that

```text
G is finitely presented, torsion-free and sofic,
K is nontrivial and has property (T),
Rad_MF(G) = K,
G/K ~= Z.                                              (TFZ1)
```

Consequently `G` is hyperlinear and non-MF, its MF radical is proper and
computed exactly, and precomposition with `G->Z` gives, for every countable
MF group `M`, a bijection

```text
Hom(Z,M) ~= Hom(G,M).                                  (TFZ2)
```

Preferred strengthening: `K` itself can be chosen finitely presented and
normally generated in `G` by one element.

The finite-presentation part of that strengthening is not a routine bonus.
By
`fp-kernel-crosses-alekseev-thom-open-problem`,
it would produce a finitely presented, sofic, property-`(T)`, non-residually-
finite group and therefore answer Alekseev--Thom Open Problem 6.1.  The base
target deliberately avoids that additional open problem: property `(T)`
already makes `K` finitely generated, but `K` need not be finitely presented.

Every witness necessarily has a sofic but non-residually-finite kernel.
Indeed `K` is a subgroup of the sofic group `G`, property `(T)` makes `K`
finitely generated, and every extension with quotient `Z` splits after
choosing a lift of `1`.  If `K` were residually finite,
`finitely-generated-rf-automorphism-mapping-torus-is-rf` would make `G`
residually finite and hence MF, contradicting its nontrivial MF radical.

The intended construction is a split extension

```text
G = K semidirectProduct_phi Z
```

with a Kazhdan subgroup `L<=G` satisfying `D_G(L)=K`.  The analytic lower
inclusion is already unconditional and kernel-checked.  The sharp remaining
obligation is an extrinsically defect-saturated, sofic but non-residually-
finite Kazhdan kernel.  It is not necessary to prove that `K` has full MF
radical before adjoining `Z`; that stronger arithmetic route remains
available separately.
