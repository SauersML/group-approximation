---
rg: 2
id: purely-infinite-unit-group-max-mf-quotient-is-k1
kind: claim
title: The maximal MF quotient of the unit group of a purely infinite simple ring is its algebraic K1
distinct_from:
  properly-infinite-unit-group-is-not-mf: that says the unit group is not MF under the weaker full-idempotent hypothesis; this computes its maximal MF quotient exactly under pure infiniteness and simplicity, and the earlier claim is the statement that this quotient is proper.
  full-defect-ring-non-mf-at-rank-two: that is total collapse for the elementary groups under a weaker ring hypothesis; this is a classification for the whole unit group, where the collapse is total exactly when K_1 vanishes.
  agp-purely-infinite-simple-k1-is-unit-abelianization: that identifies K_1 with the unit-group abelianization, an algebraic fact with no approximation content; this identifies the same group as the maximal MF quotient.
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `R` be a countable unital purely infinite simple ring.  Every
homomorphism from `R^x` to an MF group factors uniquely through

```text
kappa : R^x --> K_1(R),
```

and `ker kappa = [R^x, R^x]` itself has full MF radical.  So

```text
Rad_MF(R^x) = [R^x, R^x],       R^x / Rad_MF(R^x) = K_1(R).
```

The maximal MF quotient of the unit group is exactly the algebraic `K_1` of
the ring.  In particular `R^x` has full MF radical if and only if
`K_1(R) = 0`.

Consistency: `K_1(L_(F_2)(1,2)) = 0` recovers the total collapse recorded in
`binary-leavitt-all-ranks-full-mf-radical`.
