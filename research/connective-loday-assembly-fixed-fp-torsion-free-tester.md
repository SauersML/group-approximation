---
rg: 2
id: connective-loday-assembly-fixed-fp-torsion-free-tester
kind: claim
title: One finitely presented torsion-free group tests the entire connective integral Loday assembly
distinct_from:
  degree-one-assembly-surjective-torsion-free: that asks only for surjectivity in degree one; this concerns a weak equivalence in every connective degree.
  full-farrell-jones-fixed-fp-torsion-free-tester: that concerns the virtually-cyclic-family conjecture with coefficients, L-theory, and finite wreath products; this concerns only the integral trivial-family connective K-theory assembly.
  connective-loday-assembly-for-fixed-fp-torsion-free-tester: that is the remaining open assertion for the fixed group; this is the established equivalence with the global torsion-free assertion.
---

There exists a fixed finitely presented torsion-free group `U` such that
the connective integral Loday assembly

```text
A^U:K(NU;Z) -> K(ZU)
```

is a weak homotopy equivalence if and only if, for every torsion-free group
`G`,

```text
A^G:K(NG;Z) -> K(ZG)
```

is a weak homotopy equivalence.

Equivalently, one fixed `U` tests bijectivity of integral trivial-family
assembly simultaneously in every degree `n>=0`. This makes no assertion
about negative K-groups, arbitrary coefficient categories, the virtually
cyclic family, L-theory, finite wreath products, or Full Farrell--Jones.

The remaining open computation is
[[connective-loday-assembly-for-fixed-fp-torsion-free-tester]].

**ESTABLISHED 2026-08-30** by
[[connective-loday-fixed-tester-via-higher-whitehead-space]].
