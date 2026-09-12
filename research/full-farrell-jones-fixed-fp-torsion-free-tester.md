---
rg: 2
id: full-farrell-jones-fixed-fp-torsion-free-tester
kind: claim
title: One finitely presented torsion-free group tests Full Farrell--Jones on every torsion-free group
distinct_from:
  whitehead-universal-finitely-presented-torsion-free-group: that tests ordinary Whitehead vanishing using specially injective Whitehead maps; this tests the much stronger Full Farrell--Jones property using subgroup and directed-colimit inheritance.
  degree-one-assembly-surjective-torsion-free: that asks only for surjectivity of the integral trivial-family assembly map in degree one; Full Farrell--Jones includes all degrees, coefficient categories, L-theory, and finite wreath products.
  full-farrell-jones-for-fixed-fp-torsion-free-tester: that is the remaining open assertion for the one tester; this is the established equivalence between that assertion and the torsion-free global conjecture.
---

Let `FJ` denote the class of groups satisfying Lueck's Full
Farrell--Jones Conjecture, Definition 8.10.

There exists a fixed finitely presented torsion-free group `U` such that

```text
U belongs to FJ
  <=>
every torsion-free group belongs to FJ.
```

The group `U` may be chosen to be the witness constructed in
[[whitehead-universal-finitely-presented-torsion-free-group]].

The right-hand quantifier is essential. This does not reduce Full
Farrell--Jones for arbitrary groups to a torsion-free group, and it does not
prove either side. It isolates the remaining computation as
[[full-farrell-jones-for-fixed-fp-torsion-free-tester]].

**ESTABLISHED 2026-08-30** by
[[full-farrell-jones-fixed-tester-via-subgroups-and-colimits]].
