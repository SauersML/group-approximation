---
rg: 2
id: degree-one-assembly-single-fp-tester-equivalence
kind: claim
title: Global torsion-free degree-one assembly is exactly one finitely presented test map
distinct_from:
  degree-one-assembly-surjective-torsion-free: that is the still-open universal surjectivity assertion; this is the established reduction proving it has the same truth value as one map.
  degree-one-assembly-surjective-universal-tester: that is the remaining open surjectivity computation for the fixed tester; this proves that computation is equivalent to the global assertion.
  whitehead-universal-finitely-presented-torsion-free-group: that constructs the Whitehead-injective universal group; this translates its vanishing equivalence into degree-one assembly.
---

There exists a finitely presented torsion-free group `U` such that the
following are equivalent.

1. The single map

```text
A_1^U : H_1(BU;K(Z)) -> K_1(ZU)
```

is surjective.
2. `A_1^G` is surjective for every torsion-free group `G`.

The same `U` Whitehead-injectively contains every countably generated
recursively presented torsion-free group.

**ESTABLISHED 2026-08-30** by
[[degree-one-assembly-single-tester-proof]].
