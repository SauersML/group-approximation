---
rg: 2
id: degree-one-assembly-surjective-universal-tester
kind: claim
title: Degree-one assembly is surjective for the universal finitely presented torsion-free tester
distinct_from:
  degree-one-assembly-surjective-torsion-free: that quantifies over every torsion-free group; this is one finitely presented test map, although the established equivalence proves they have the same truth value.
  degree-one-assembly-single-fp-tester-equivalence: that is the established reduction; this is the remaining open computation it isolates.
  whitehead-universal-finitely-presented-torsion-free-group: that establishes the universal embedding property but does not assert Whitehead vanishing or assembly surjectivity for the host.
---

**OPEN.** For a finitely presented torsion-free universal tester `U` from
[[whitehead-universal-finitely-presented-torsion-free-group]], the map

```text
A_1^U : H_1(BU;K(Z)) -> K_1(ZU)
```

is surjective.

By [[degree-one-assembly-single-fp-tester-equivalence]], this single
computation is exactly equivalent to degree-one surjectivity for every
torsion-free group.
