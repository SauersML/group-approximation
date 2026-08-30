---
rg: 2
id: sofic-quotient-nonclosure-via-universal-test-group
kind: route
title: Present the universal nonsofic tester as a finite-relator quotient of F2
target: sofic-quotient-nonclosure
requires:
  - universal-local-approximation-fixed-two-generator-test-group
  - fp-quotient-iff-kernel-finitely-normally-generated
artifacts:
  - GroupApproximation/Endpoint/MainResults.lean
---

Let `V` be the fixed two-generator finitely presented group supplied by
[[universal-local-approximation-fixed-two-generator-test-group]]. That result
also proves that `V` is nonsofic. Choose, once and for all, two generators
`v_1,v_2` and the resulting epimorphism

```text
pi : F_2 = F(a,b) ->> V,
pi(a)=v_1,  pi(b)=v_2.
```

Put `N = ker(pi)`. Both `F_2` and `V` are finitely presented, so
[[fp-quotient-iff-kernel-finitely-normally-generated]] shows that `N` is
finitely normally generated. Choose a finite set
`R={r_1,...,r_m} subseteq F_2` with `N=<<R>>`. Because `V` was fixed before
any approximation property was chosen, this gives a fixed finite presentation

```text
V ≅ F_2/<<R>> = <a,b | r_1,...,r_m>.
```

The free group `F_2` is residually finite and hence sofic: for any finite
subset, choose a finite quotient separating all its pairwise differences and
use the left-regular action of that quotient as an exact finite model. The
target `V` is nonsofic by the first prerequisite. Therefore `pi` is a
finite-relator quotient from a sofic group to a nonsofic group.

The unrestricted nonclosure statement is already formalized as
`Endpoint/MainResults.exists_sofic_with_nonsofic_quotient`. Its formal source
is the free group on the underlying type of an arbitrary nonsofic witness;
the present argument sharpens that result to the fixed rank-two source and a
finitely normally generated kernel. QED
