---
rg: 2
id: torsion-freeness-recognition-is-pi2-complete
kind: claim
title: Torsion-freeness is Pi-zero-two complete for two-generator recursive presentations and for enumerated presentations
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  amenability-two-generator-recursive-is-pi2-complete: that classifies amenability, whose upper bound is Kesten's criterion; this classifies torsion-freeness, whose upper bound is a universal quantifier over a difference of two recursively enumerable events, and whose hardness needs only a finite forbidden seed rather than a right-angled Artin family.
  second-level-rice-theorem-for-local-approximation-properties: that covers properties containing the residually finite groups; torsion-freeness fails for finite groups, so it is not of that shape and needs the isomorphism-invariant form of the switch.
---

ESTABLISHED.  Call `G` torsion-free if `g^n = 1` with `n >= 1` forces
`g = 1`.  For two-generator recursive presentations and for countably
generated enumerated presentations,

```text
TORSIONFREE  is Pi^0_2-complete,     its complement Sigma^0_2-complete.   (TF1)
```

**Upper bound.**  `G` is torsion-free iff for every word `w` and every
`n >= 1`, `w^n = 1` implies `w = 1`.  Both `w^n = 1` and `w = 1` are r.e.
(the word problem of a recursive presentation), so each instance is a
`Delta^0_2` condition (`Pi^0_1 or Sigma^0_1`), hence `Pi^0_2`; the class
`Pi^0_2` is closed under universal number quantification, so the whole is
`Pi^0_2`.

**Hardness.**  Torsion-freeness is isomorphism invariant, holds for the
trivial group and fails for `Z/2`, which is finitely presented; the
parametric switch of
[[arbitrary-forbidden-seed-hereditary-property-switch]] with seed `Z/2`
has value `1` on `INF` and `Z/2` on `FIN`, so `INF` many-one reduces to
`TORSIONFREE`.  For two generators, apply the bidirectional bridge, whose
value on the trivial group is `B2(1)`, a subgroup of `F_2 x F_2` hence
torsion-free, while on `FIN` the output contains `Z/2`.

**Consequence.**  Torsion-freeness, soficity, hyperlinearity (side (B)),
operator-MF, LEF, amenability, commutativity and triviality all sit at
`Pi^0_2` on recursive presentations; property (T) at `Sigma^0_1`; residual
finiteness at `Pi^0_3`.  See
[[arithmetical-complexity-table-of-group-properties]] and
[[natural-group-properties-realize-the-first-three-levels]].
