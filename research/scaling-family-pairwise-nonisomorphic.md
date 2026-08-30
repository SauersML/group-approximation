---
rg: 2
id: scaling-family-pairwise-nonisomorphic
kind: claim
title: Pairwise non-isomorphism of the non-MF scaling family
root: true
distinct_from:
  scaling-family-non-mf: The established claim proves non-MF for every scale but does not distinguish the abstract isomorphism types.
  continuum-nonisomorphic-non-mf-cylinder: This claim distinguishes the explicit countable scaling family; the other asks for a continuum-sized family in the marked-group cylinder.
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
  - research/artifacts/scaling-family-invariants-audit-2026-08-30.md
---

**ESTABLISHED.**  The finitely presented non-MF groups `E_m), for integers
`m>=2`, are pairwise non-isomorphic.

The intrinsic datum is the commensurability class of subgroups isomorphic to

```text
B=Z^3 semidirect SL_3(Z)
```

and commensurated by the whole group.  Cubical fixed-point rigidity and the
Margulis--Zimmer theorem force every such subgroup of `E_m` to be
commensurable with the displayed affine base.  Its relative modular
homomorphism has image

```text
Delta_B(E_m)=<m^3> <= Q_(>0).
```

This image is unchanged under abstract isomorphism or replacement of `B` by
a commensurable subgroup.  Hence `E_m~=E_n` forces
`<m^3>=<n^3>`, and therefore `m=n`.

The earlier prime-block theorem remains an independent finite-radical
certificate on the prime subfamily: for prime `p`, maximal
property-`(T)` subgroups have finite radical of order `2^(p^3+1)`.

DERIVATION
[[scaling-family-pairwise-nonisomorphic-via-hecke-modulus]]
