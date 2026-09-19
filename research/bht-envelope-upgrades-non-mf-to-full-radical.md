---
rg: 2
id: bht-envelope-upgrades-non-mf-to-full-radical
kind: claim
title: A BHT normal-intersection envelope upgrades any non-MF seed to a finitely presented quotient-hereditary full MF radical
distinct_from:
  bht-trivial-normal-intersection-envelope: that is the universal embedding theorem and contains no approximation property; this applies its normal-intersection conclusion to an arbitrary non-MF input and obtains full MF radical for the ambient finitely presented group and every nontrivial quotient.
  simple-sofic-total-mf-radical: that embeds one particular sofic non-MF witness in a countable simple sofic group; this is a conditional theorem for every finitely generated solvable-word-problem non-MF seed, produces a finitely presented ambient group, and controls all of its nontrivial quotients without asserting soficity.
  defect-saturation-full-mf-radical: that constructs a torsion-free finitely presented full-radical group by a Kazhdan compression and small-cancellation route; this is a Property-(T)-free inheritance theorem whose non-MF seed remains an explicit hypothesis.
artifacts:
  - research/artifacts/property-t-free-mf-envelope-calculus-2026-08-30.md
---

Let `Gamma` be a finitely generated non-MF group with solvable word problem.
There is a finitely presented group `P` containing `Gamma` such that

```text
Rad_MF(P)=P,                                             (BMS1)
```

and, more strongly, every nontrivial quotient `Q` of `P` satisfies

```text
Rad_MF(Q)=Q.                                             (BMS2)
```

Equivalently, every homomorphism from `P`, or from any quotient of `P`, to
an MF group is trivial.  In particular every nontrivial quotient of `P` is
non-MF.

The group `P` has a maximal proper normal subgroup `M`; every such choice
gives a finitely generated simple non-MF quotient `P/M` which still contains
`Gamma` and has full MF radical.  Moreover

```text
P/M is finitely presented
  <=>
M is finitely normally generated in P.                  (BMS3)
```

No Property `(T)`, Kazhdan subgroup, Kazhdan projection, trace, stability,
or compression input occurs in this theorem.  It is an inheritance and
saturation result: the hypothesis that `Gamma` is non-MF is not discharged.

DERIVATION
bht-envelope-upgrades-non-mf-to-full-radical-proof
