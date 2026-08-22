---
rg: 2
id: leavitt-corner-witness-has-unitized-rank-floor
kind: claim
title: Any Leavitt corner one-sided inverse unitizes beyond the known modular rank pairs
distinct_from:
  leavitt-rank-three-lift-inverse-support-thirteen: that concerns one fixed support-three lift in the whole group algebra and is now vacuous because that lift has no inverse; this gives necessary support profiles for every possible witness in the Leavitt corner.
  leavitt-rank-three-lift-has-no-one-sided-inverse: that uses support location in a virtually free subgroup to kill one candidate at all ranks; this uses only universal rank-pair direct-finiteness bounds and applies to every corner candidate.
  dykema-heister-juschenko-bounded-rank-direct-finiteness: that is the imported theorem for arbitrary group-algebra pairs with product one; this performs the nontrivial unitization and nonunit evaluation checks needed to apply it inside the augmentation-zero Leavitt corner.
artifacts:
  - research/artifacts/leavitt-corner-unitized-rank-floor-2026-08-21.md
---

Let `S=F_2[R^x]`, `e=[g]+[g^2]`, and `z=1+e=[1]+[g]+[g^2]`.  If
`a,b in eSe` satisfy

```text
ab=e,             pi(ba)!=1,
```

then the unitized elements

```text
alpha=a+z,        beta=b+z
```

satisfy `alpha beta=1!=beta alpha`.  Their actual group-basis support sizes
are odd and at least three.  Moreover:

1. if either has support three, the other has support at least thirteen;
2. they cannot both have support five.

Hence, after ordering the two ranks, every corner witness has unitized support
profile at least `(3,13)` or `(5,7)` (or larger).  In particular the minimum
possible total unitized support is twelve and the minimum possible maximum
support is seven.
