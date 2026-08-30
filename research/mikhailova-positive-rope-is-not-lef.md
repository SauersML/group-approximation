---
rg: 2
id: mikhailova-positive-rope-is-not-lef
kind: claim
title: The fixed positive Mikhailova rope is not LEF
distinct_from:
  the-mikhailova-rope-object-card: that inventories every property of the compiler's positive group; this closes one entry of that inventory by a finite-presentation argument.
  centralizing-hnn-sofic-via-regular-edge-centralizer: that proves exact finite quotient models kill closure-point pinches but leaves approximate permutation models alive; this upgrades the exact obstruction to all LEF charts without claiming nonsoficity.
  mf-safe-finite-presentation-compiler: that proves the same rope is operator-MF; this separates its operator-norm matrix approximation from exact finite-group approximation.
---

ESTABLISHED.  Let `R` be the positive-branch group of
[[the-mikhailova-rope-object-card]].  Then

```text
R is finitely presented, operator-MF and torsion-free,
but R is not LEF.                                           (MPRL1)
```

Indeed the first rope stage is

```text
Gamma=<K,v | [v,L]=1>,                                     (MPRL2)
```

where `K` is a finite direct product of finite-rank free groups and `L` is a
finitely generated Mikhailova-type edge.  The edge is not profinitely closed:
membership in its Mikhailova factor is undecidable, whereas membership in a
finitely generated separable subgroup of a finitely presented group is
decidable by dovetailing word proofs with finite-quotient certificates.
Therefore [[finitely-presented-centralizing-hnn-lef-criterion]] says that
`Gamma` is not LEF.

The final graph-valued HNN step contains its base, hence contains `Gamma`, by
Britton normal form.  Since LEF is inherited by subgroups, `R` cannot be LEF.
This obstruction is compatible with the compiler's MF theorem and does not
settle soficity: a sofic approximation may be genuinely approximate and need
not contain any exact local embedding into a finite group.

DERIVATION
[[mikhailova-positive-rope-not-lef-proof]]
