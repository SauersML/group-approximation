---
rg: 2
id: wave3-audit-h31-abelian-sylow-images
kind: claim
title: The finite images of H31 with abelian Sylow five subgroups are exactly four groups
distinct_from:
  h31-finite-quotients-have-no-seven-schur-class: that asks for vanishing over all finite images; this classifies only those whose Sylow five subgroups are abelian.
artifacts:
  - research/artifacts/hyperbolic-rf-wave3-audit-2026-09-20.md
---

Let `Q=PSL_2(31)` and let `H_31` have the presentation specified in
[[h31-seven-central-image-criterion]]. Its finite quotient groups with
abelian Sylow `5` subgroups, up to isomorphism, are exactly

```
1, C_5, Q, Q x C_5.
```

Every homomorphism from `H_31` to any finite group with abelian Sylow
`5` subgroups factors through the explicit quotient
`H_31 -> Q x C_5` sending `a,b` to the standard generators of `Q`
and `c` to the central generator of `C_5`.

In particular every finite image with nontrivial central `7` torsion
must have nonabelian Sylow `5` subgroups. Every homomorphism into
`PSL_2(q)` has image among the four groups above, because Sylow `5`
subgroups of `PSL_2(q)` are abelian for every prime power `q`.
No claim is made about targets with nonabelian Sylow `5` subgroups.

DERIVATION
wave3-audit-h31-abelian-sylow-proof
