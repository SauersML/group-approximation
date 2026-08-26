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
  - research/mapping-torus-mf-radical-lies-in-finite-residual.md
  - research/exact-kazhdan-radical-kernel-cannot-be-lef.md
  - research/torsion-free-sofic-extrinsic-kazhdan-defect-kernel.md
  - research/fp-kernel-crosses-alekseev-thom-open-problem.md
  - research/artifacts/torsion-free-exact-radical-team-audit-2026-08-26.md
  - research/artifacts/torsion-free-exact-radical-breakthrough-round2-2026-08-26.md
  - research/titz-witzel-mapping-tori-are-virtually-products.md
  - research/titz-witzel-exact-kazhdan-mf-radical-over-z.md
  - research/titz-witzel-soficity-is-one-finite-csp.md
  - research/titz-witzel-sofic-gate-two-generators-four-approximate-relators.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
  - research/artifacts/torsion-free-exact-radical-breakthrough-2026-08-26.md
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

Every witness necessarily has a sofic kernel with no nontrivial finite
quotient.  This is much stronger than non-residual-finiteness.
Indeed `K` is a subgroup of the sofic group `G`, property `(T)` makes `K`
finitely generated, and every extension with quotient `Z` splits after
choosing a lift of `1`.  By
`mapping-torus-mf-radical-lies-in-finite-residual`, the MF radical of the
resulting mapping torus is contained in the finite residual of `K`.  Equality
with `K` therefore forces the finite residual to be all of `K`.

Moreover, the kernel can never be LEF.  Indeed LEF implies operator-MF, and
the Dadarlat--Ozawa--Thom theorem gives every infinite operator-MF Kazhdan
group an infinite residually finite quotient.  Such a quotient produces a
nontrivial finite quotient, contradicting the previous paragraph.  Thus the
required kernel occupies the genuinely approximate region

```text
sofic but non-LEF, property (T), and no nontrivial finite quotient.
```

In particular, no marked limit of finite groups can supply it; this closes
the former alternating-mother branch.  See
`exact-kazhdan-radical-kernel-cannot-be-lef`.

The intended construction is a split extension

```text
G = K semidirectProduct_phi Z
```

with a Kazhdan subgroup `L<=G` satisfying `D_G(L)=K`.  The analytic lower
inclusion is already unconditional and kernel-checked.  The sharp remaining
obligation is an extrinsically defect-saturated, sofic Kazhdan kernel with no
nontrivial finite quotient.  It is not necessary to prove that `K` has full MF
radical before adjoining `Z`; that stronger arithmetic route remains
available separately.

The surviving candidates are now sharply separated.  Proving soficity of the
arithmetic single-defect saturated group would solve the target by taking its
direct product with `Z`; this would also cross Alekseev--Thom Open Problem 6.1.
For a Titz--Witzel simple Kazhdan lattice, every cyclic mapping torus is
virtually a direct product because its outer automorphism group is finite.
The kernel is already unconditionally non-MF with full MF radical by
`simple-kazhdan-groups-have-full-mf-radical`.  That route therefore succeeds
exactly when one such lattice is proved sofic.  The original twelve-equation
finite-permutation gate `titz-witzel-soficity-is-one-finite-csp` is now
Tietze-reduced by
`titz-witzel-sofic-gate-two-generators-four-approximate-relators` to one
exact involution, one arbitrary permutation, four approximate equations and
the separated word `u^8`.  The Elek--Szabo simple sofic
envelope supplies neither
torsion-free nor Kazhdan control.  No construction presently in Cairn or in
the audited primary sources closes any of these surviving seams.

In particular, `titz-witzel-exact-kazhdan-mf-radical-over-z` proves
unconditionally every clause of `(TFZ1)` and `(TFZ2)` except soficity and the
consequent hyperlinearity assertion: taking `G=K x Z` already gives finite
presentation, torsion-freeness, the exact proper Kazhdan radical, quotient
`Z`, non-MF, finite presentation of `K`, and one-element normal generation.
