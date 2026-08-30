---
rg: 2
id: affine-scaling-hnn-groups-pairwise-nonisomorphic
kind: claim
title: The affine scaling HNN groups remember the exact dilation integer
distinct_from:
  scaling-family-pairwise-nonisomorphic: This distinguishes the canonical affine retracts H_m of E_m; passing the invariant through the non-MF lamp kernel still requires that quotient to be intrinsic in E_m.
  scaling-family-abelianization-is-constant: That proves the full E_m abelianizations are all equal; this uses the characteristic normal module and its quotient action instead.
artifacts:
  - non_mf_group_notes.tex
  - research/artifacts/scaling-family-invariants-audit-2026-08-30.md
---

Let

```text
B = Z^3 semidirect SL_3(Z),
alpha_m(u,A)=(m u,A),
H_m = < B,t | t b t^(-1)=alpha_m(b), b in B >
```

for `m>=2`.  Then `H_m ~= H_n` if and only if `m=n`.

More intrinsically, the direct-limit translation module

```text
U_m = Z[1/m]^3
```

is the unique largest normal abelian subgroup of `H_m`, hence is
characteristic.  The center of `H_m/U_m ~= SL_3(Z) direct_product Z` is
the stable-letter factor.  Its conjugation action on `U_m` is multiplication
by `m`, and this recovers `m` from the abstract group.
