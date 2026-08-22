---
rg: 2
id: sl3-hnn-symmetric-double-proof
kind: route
title: Normal form embeds the HNN group and Shulman's theorem stops at trace-blind MF
target: sl3-hnn-sits-in-shulman-symmetric-double
requires:
  - shulman-amalgam-mf-criterion
  - shulman-symmetric-double-has-no-stable-trace-upgrade
artifacts:
  - research/artifacts/sl3-hnn-symmetric-double-mf-firewall-2026-08-21.md
---

The artifact gives the full normal-form proof.  Inside

```text
(A x Z) *_C (A x Z)
```

the subgroups `A` in the first factor and `C x Z` in the second factor
intersect the amalgam in exactly `C`; hence every reduced word of
`A *_C (C x Z)` remains reduced in the double.  This proves injectivity.

`shulman-amalgam-mf-criterion` applies Theorem 10 to the full group C-star
algebra of the symmetric double and yields only operator-norm algebra MF,
then group-MF after restriction.  The source-scope theorem
`shulman-symmetric-double-has-no-stable-trace-upgrade` proves that no
prescribed-trace conclusion is present.  In particular this argument does
not construct canonical-trace microstates for the HNN subgroup; the missing
upgrade is exactly the nonamenable amalgamated-free trace problem.

